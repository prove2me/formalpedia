-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P99_complementary_coin_concentration
-- name    : QAlgorithms.Papers.Independent.Intake100.P99.complementary_coin_concentration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:12:00.846481+00:00
-- url     : https://prove2.me/theorems/baf1e4ec-9294-42fc-8a7e-bf395427b908
-- title:
--   Complementary measurement concentration for quantum coins
-- statement:
--   Let $\rho_n$ be any family of normalized, possibly mixed states of $n$ qubits, and let $0\leq\Delta\leq\tfrac12$. Write $N_X$ and $N_Z$ for the counts of minus outcomes when all coins are measured in the $X$ or $Z$ basis, respectively. Let $f(\Delta)\in[0,\tfrac12]$ be the unique solution of $H_2(\tfrac12-f(\Delta))+H_2(\Delta)=1$, where $H_2$ is binary entropy in bits with $0\log 0=0$. If $\Pr_{\rho_n}[N_X\geq n\Delta]$ is exponentially small in $n$, then, for every fixed $\varepsilon>0$,
--
--   $$
--   \Pr_{\rho_n}\!\left[\left|\frac n2-N_Z\right|\geq n(f(\Delta)+\varepsilon)\right]\leq e^{-Cn}\qquad(n\geq n_0)
--   $$
--
--   for some $C>0$ and $n_0$. These constants may depend on the state family, the disturbance bound, and the chosen slack. This transfers concentration between complementary coin measurements without an independence assumption.
--
--   **Formalization Note** The displayed strict premise of the source is retained: at $\Delta=0$ it cannot hold with high probability; $n=0$ is irrelevant to an eventual bound.
-- source:
--   Security of quantum key distribution with imperfect devices, arXiv:quant-ph/0212066v3, PDF p. 11, Lemma 1: complementary measurement concentration for quantum coins

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P99

noncomputable section

open scoped Matrix ComplexConjugate BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P99

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation receiver)

/-- arXiv:quant-ph/0212066v3, PDF p.11, Lemma 1 and (19)--(20).
The family formulation preserves exponential high probability and mixed states.
At delta=0 its printed strict premise is vacuous, as in the source. -/
theorem complementary_coin_concentration
    (delta : ℝ) (hdelta : 0 ≤ delta ∧ delta ≤ 1 / 2)
    (rho : (n : ℕ) → Matrix (Qubits n) (Qubits n) ℂ)
    (hstate : ∀ n, IsDensityMatrix (rho n))
    (hX : ExponentiallySmall (fun n => coinXFailure (rho n) delta)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ExponentiallySmall (fun n => coinZFailure (rho n) delta epsilon) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P99

end
