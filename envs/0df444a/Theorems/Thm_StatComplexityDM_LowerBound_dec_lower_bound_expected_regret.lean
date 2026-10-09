-- Prove2me | Theorems.Thm_StatComplexityDM_LowerBound_dec_lower_bound_expected_regret
-- name    : StatComplexityDM.LowerBound.dec_lower_bound_expected_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:38.417868+00:00
-- url     : https://prove2.me/theorems/9ce64e31-119d-4d0e-9de3-76f906f4423f
-- title:
--   Theorem 3.2, (13), p. 12 — every algorithm has sup_M E^M[Reg_DM] ≥ 6⁻¹·dec_γ(M^∞_ε̄γ(M̄), M̄)·T, C(T) = 2¹¹log(2T ∧ V(M))
-- statement:
--   Let $\mathcal M$ be a nonempty class of models whose mean-reward functions take values in $[0,1]$ ($\mathcal F_{\mathcal M}\subseteq(\Pi\to[0,1])$), and let $T\ge1$. Define $C(T)=2^{11}\log(2T\wedge V(\mathcal M))$, where $V(\mathcal M)$ is the class density ratio (cut off below by $e$, possibly $+\infty$), and $\bar\varepsilon_\gamma=C(T)^{-1}\gamma/T$. Then for every adaptive algorithm $p$ of horizon $T$, every $\gamma>0$ and every $\bar M\in\mathcal M$,
--
--   $$
--   \sup_{M\in\mathcal M}\mathbb E^{M,p}\bigl[\mathrm{Reg}_{\mathrm{DM}}\bigr]\ \ge\ 6^{-1}\cdot\mathrm{dec}_\gamma\bigl(\mathcal M^\infty_{\bar\varepsilon_\gamma}(\bar M),\bar M\bigr)\cdot T .
--   $$
--
--   The localized decision-estimation coefficient is therefore a lower bound on the minimax expected regret of interactive decision making, for any model class; together with the upper bounds of the paper it characterizes the statistical complexity of the problem.
--
--   **Formalization Note** Decisions $\Pi$ and joint reward–observation outcomes $\mathcal R\times\mathcal O$ are finite alphabets (the finite-alphabet case of the paper's measurable setting, §2, p. 9); models and algorithm kernels are probability vectors and expectations are finite sums. The page states that some model in $\mathcal M$ has expected regret at least $6^{-1}\max_{\gamma>0}\sup_{\bar M}\mathrm{dec}_\gamma(\cdots)T$; its proof (p. 90) takes a model attaining a supremum "or a limit sequence" when it is not attained, which yields the bound on $\sup_{M\in\mathcal M}\mathbb E^M[\mathrm{Reg}_{\mathrm{DM}}]$ stated here. The $\max_\gamma\sup_{\bar M}$ becomes "for every $\gamma>0$ and $\bar M\in\mathcal M$", which is equivalent for a lower bound. Expected regret is (1): it averages the gap under the distribution $p^{(t)}(\cdot\mid\mathcal H^{(t-1)})$ chosen from the past, not under the realized decision. Event ratios with zero denominator are $+\infty$, so $V(\mathcal M)=+\infty$ is covered.
-- source:
--   arXiv:2112.13487v3, Theorem 3.2, (13), p. 12; proof App. C.1.3, pp. 90–91

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_History
import Definitions.Def_FoundationsRL_GeneralDM_DEC

namespace StatComplexityDM.LowerBound

open FoundationsRL.GeneralDM

/-- Theorem 3.2, (13), p. 12, with the supremum form justified in App. C.1.3. -/
theorem dec_lower_bound_expected_regret {S Y : Type*} [Fintype S] [Fintype Y]
    [Nonempty S] [DecidableEq Y]
    (rew : Y → ℝ) (𝓜 : Set (S → Y → ℝ))
    (h𝓜 : ∀ m ∈ 𝓜, IsModel m) (h𝓜ne : 𝓜.Nonempty)
    (piStar : (S → Y → ℝ) → S) (hpiStar : IsArgmaxSel rew piStar)
    (hF : ∀ m ∈ 𝓜, ∀ π, 0 ≤ fM rew m π ∧ fM rew m π ≤ 1)
    (T : ℕ) (hT : 1 ≤ T)
    (alg : (t : Fin T) → History S Y t.val → S → ℝ)
    (halg : IsAlgorithm alg) :
    ∀ γ : ℝ, 0 < γ → ∀ mbar ∈ 𝓜,
      (1 / 6 : ℝ) *
        decGf (linfLocalized 𝓜 rew piStar mbar
          (γ / (regretConstant 𝓜 T * (T : ℝ)))) rew piStar γ mbar * (T : ℝ) ≤
        sSup ((fun m : S → Y → ℝ => expRegret rew piStar m alg) '' 𝓜) := by sorry

end StatComplexityDM.LowerBound
