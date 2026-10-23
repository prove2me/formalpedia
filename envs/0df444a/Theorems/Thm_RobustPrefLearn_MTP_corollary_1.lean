-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_corollary_1
-- name    : RobustPrefLearn.MTP.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:07.822581+00:00
-- url     : https://prove2.me/theorems/01757e8a-e3ea-422f-9c4c-dbef45db257d
-- title:
--   Corollary 1, p. 15 — I^OA_* = I_*(f) = max_λ min over OA alternatives, for every OA preference f
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. For every $f\in\mathcal M^{\mathrm{OA}}_p$,
--   $$I^{\mathrm{OA}}_*=I_*(f)=\max_{\lambda\in\Delta(\mathcal S)}\ \min_{\bar f\in\overline{\mathcal M}^{\mathrm{OA}}_p(f)} D_\lambda(f\|\bar f),$$
--   and the maximum over $\lambda$ is attained.
--
--   So for an OA preference it suffices to consider OA alternatives, a finite set; this is what makes the stopping rule of the Myopic Tracking Policy computable.
--
--   **Formalization Note** Versions $1,\dots,K$ are `Fin K` (version $m$ is `⟨m-1, _⟩`), and a ranking `σ : Equiv.Perm (Fin K)` sends a version to its rank **0-based**, so `σ X = 0` is the paper's $\sigma(X)=1$. The statement has three parts: the two equalities and the attainment of the maximum (the minimum is over a finite set). The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 15, Corollary 1

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-- Corollary 1, p. 15. For every `f ∈ M^OA_p`,
`I^OA_* = I_*(f) = max_{λ ∈ Δ(𝒮)} min_{f̄ ∈ M̄^OA_p(f)} D_λ(f‖f̄)`, the maximum being attained. -/
theorem corollary_1 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : Pref K) (hf : f ∈ (MOA p : Set (Pref K))) :
    IOA (K := K) p = Istar p f ∧
    Istar p f = (⨆ lam ∈ simplex K, ⨅ g ∈ altOA p f, ENNReal.ofReal (Dlam lam f g)) ∧
    ∃ lam ∈ simplex K, Istar p f = ⨅ g ∈ altOA p f, ENNReal.ofReal (Dlam lam f g) := by sorry

end RobustPrefLearn.MTP
