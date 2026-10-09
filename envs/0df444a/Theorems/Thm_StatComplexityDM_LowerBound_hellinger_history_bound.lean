-- Prove2me | Theorems.Thm_StatComplexityDM_LowerBound_hellinger_history_bound
-- name    : StatComplexityDM.LowerBound.hellinger_history_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:24.583978+00:00
-- url     : https://prove2.me/theorems/f467928e-7971-494a-80e0-7b258125efd8
-- title:
--   App. C.1.3, p. 90 — Lemma A.13 on histories: D²_H(P^M, P^M̄) ≤ C_T Σ_t E^M̄[D²_H(M(π⁽ᵗ⁾), M̄(π⁽ᵗ⁾))]
-- statement:
--   Let $M,\bar M\in\mathcal M$ be models and $p$ an adaptive algorithm of horizon $T\ge1$, and let $\mathbb P^{M}$, $\mathbb P^{\bar M}$ be the laws of the history $\mathcal H^{(T)}$ when $p$ runs on $M$ and on $\bar M$. Then
--
--   $$
--   D^2_{\mathrm H}\bigl(\mathbb P^{M},\mathbb P^{\bar M}\bigr)\le C_T\sum_{t=1}^T\mathbb E^{\bar M}\Bigl[\mathbb E_{\pi\sim p^{(t)}(\cdot\mid\mathcal H^{(t-1)})}\bigl[D^2_{\mathrm H}(M(\pi),\bar M(\pi))\bigr]\Bigr],
--   $$
--
--   with $C_T=2^8\log\bigl(2T\wedge(V^{\bar M}(\mathcal M)\vee e)\bigr)$ and $V^{\bar M}(\mathcal M)=\sup_{M'\in\mathcal M}\sup_\pi\sup_A\bar M(A\mid\pi)/M'(A\mid\pi)$. The right side equals $C_T\,T\,\mathbb E_{\pi\sim p_{\bar M}}[D^2_{\mathrm H}(M(\pi),\bar M(\pi))]$.
--
--   The inequality transfers the one-step discrepancy between two models, measured under the reference model's play, to the whole adaptive history; it is Lemma A.13 applied to the $2T$-step sequence $\pi^{(1)},(r^{(1)},o^{(1)}),\dots$, whose decision kernels coincide under both models (footnote 26, p. 88).
--
--   **Formalization Note** Decisions $\Pi$ and joint reward–observation outcomes $\mathcal R\times\mathcal O$ are finite alphabets (the finite-alphabet case of the paper's measurable setting, §2, p. 9); models and algorithm kernels are probability vectors and expectations are finite sums. The page writes $C_T=2^8(\log(2T)\wedge\log V^{\bar M}(\mathcal M))$; Lemma A.13 (98), from which it comes, requires $V\ge e$, so the formalization uses $V^{\bar M}(\mathcal M)\vee e$. Without the cutoff the statement is false: for $T=1$ the left side equals $\mathbb E_{\pi\sim p}[D^2_{\mathrm H}(M(\pi),\bar M(\pi))]$, while $2^8\log V^{\bar M}(\mathcal M)<1$ for two Bernoulli models with means $\tfrac12$ and $\tfrac12+\delta$ and small $\delta$. Event ratios with positive numerator and zero denominator are $+\infty$.
-- source:
--   arXiv:2112.13487v3, App. C.1.3, proof of Theorem 3.2, p. 90; footnote 26, p. 88; Lemma A.13 (97)–(98), p. 73

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_History

namespace StatComplexityDM.LowerBound

open FoundationsRL.GeneralDM

/-- App. C.1.3, p. 90: Lemma A.13 for the alternating decision–outcome history. -/
theorem hellinger_history_bound {S Y : Type*} [Fintype S] [Fintype Y] [Nonempty S]
    [DecidableEq Y] (𝓜 : Set (S → Y → ℝ))
    (h𝓜 : ∀ m ∈ 𝓜, IsModel m) (m mbar : S → Y → ℝ)
    (hm : m ∈ 𝓜) (hmbar : mbar ∈ 𝓜) (T : ℕ) (hT : 1 ≤ T)
    (alg : (t : Fin T) → History S Y t.val → S → ℝ)
    (halg : IsAlgorithm alg) :
    hellingerSq (histLaw m alg) (histLaw mbar alg) ≤
      historyConstant 𝓜 mbar T *
        ∑ h : History S Y T, histLaw mbar alg h *
          ∑ t : Fin T, ∑ π : S,
            alg t (historyPrefix h t) π * hellingerSq (m π) (mbar π) := by sorry

end StatComplexityDM.LowerBound
