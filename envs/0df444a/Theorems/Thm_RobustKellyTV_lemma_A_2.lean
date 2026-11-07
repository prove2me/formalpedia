-- Prove2me | Theorems.Thm_RobustKellyTV_lemma_A_2
-- name    : RobustKellyTV.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:09.727104+00:00
-- url     : https://prove2.me/theorems/b6acb047-cadf-496d-8861-6e30b4559986
-- title:
--   Lemma A.2 — logarithmic envelope $\max_i|\log E_U(i)|\le C+\log(T+1)$
-- statement:
--   Fix a nominal law $P$ and positive pseudocounts $\alpha$. There is a constant $C<\infty$, depending only on $P$ and $\alpha$, such that for every radius $\epsilon_0$ satisfying the standing assumptions, every $T$ and every count vector $N$ with $\sum_iN_i=T$, the smoothed empirical predictor $U=(N+\alpha)/(T+\alpha_+)$ satisfies
--
--   $$\max_i|\log E_U(i)|\le C+\log(T+1).$$
--
--   This envelope controls the increments of $\log M^{\mathrm{CK}}$ in the stopping-time analysis.
--
--   Differences from the source:
--   - reading: C depending only on P and α; every smoothed empirical predictor based on T observations → ∃ C after P and the pseudocounts, before the setting's ϵ0, T and the counts; predictor (N + α)/(T + α_+) with Σ N_i = T; reason: the dependence stated in the lemma and the predictor of (15)
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, Appendix A.1, Lemma A.2, p.23

import Mathlib
import Definitions.Def_RobustKellyTV_Mck

namespace RobustKellyTV

/-- **Lemma A.2** (Logarithmic envelope). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Lemma A.2, p.23.

There is a constant `C < ∞`, depending only on `P` and `α`, such that every smoothed empirical
predictor based on `T` observations satisfies `maxᵢ |log E_U(i)| ≤ C + log(T + 1)`.

**Formalization Note.** `α` is the pseudocount vector `pc` (positive). The constant is chosen after
`P` and `α` and before the radius `ϵ0` (any setting with nominal law `P`), `T` and the counts. A
smoothed empirical predictor based on `T` observations is `U = (N + α)/(T + α₊)` for a count vector
`N` with `Σᵢ Nᵢ = T`. -/
theorem lemma_A_2 {d : ℕ} (P pc : Fin d → ℝ) (hpc : ∀ i, 0 < pc i) :
    ∃ C : ℝ, ∀ σ : Setting d, σ.P = P → ∀ (T : ℕ) (N : Fin d → ℕ), ∑ i, N i = T →
      ∀ i, |Real.log (oracleE σ (smoothed pc N T) i)| ≤ C + Real.log ((T : ℝ) + 1) := by sorry

end RobustKellyTV
