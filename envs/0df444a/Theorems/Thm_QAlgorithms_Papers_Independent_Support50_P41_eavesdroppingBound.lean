-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_eavesdroppingBound
-- name    : QAlgorithms.Papers.Independent.Support50.P41.eavesdroppingBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:29:46.42259+00:00
-- url     : https://prove2.me/theorems/5fa5ad11-ce0c-4643-abd0-bc7e0b752508
-- title:
--   §5.3, equations (20)–(21): accessible information bounded by entropy production
-- statement:
--   Let $p_k$ be a countable probability law and $\rho_k$ density matrices on a nonzero finite-dimensional system. Apply one fixed unitary interaction with an initially independent pure finite environment, inducing the same channel $\Phi$ for all $k$. Put $\bar\rho=\sum_k p_k\rho_k$, and let $\sigma_k$ and $\bar\sigma$ be the corresponding environment outputs. Every countable POVM on that environment, with preparation label $X$ and outcome $Y$, satisfies
--
--   $$I(X:Y)\le S(\bar\sigma)-\sum_k p_k S(\sigma_k)
--   =S_e(\bar\rho,\Phi)-\sum_k p_k S_e(\rho_k,\Phi)\le S_e(\bar\rho,\Phi).$$
--
--   The matrix average and conditional entropy series converge. Mutual information is a nonnegative relative-entropy sum in bits, permitting infinite marginal Shannon entropies. A measurement on part of the environment is included as a POVM on the full environment.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 25, §5.3, equations (20)–(21): accessible information bounded by entropy production

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- PDF pp.24--25, (20)--(21): countable preparation ensemble and countable measurement on a pure environment. -/
theorem eavesdroppingBound {K Y : Type*} [Countable K] [Countable Y]
    {d e : ℕ} [NeZero d] [NeZero e]
    (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ)
    (eta : EuclideanSpace ℂ (Fin e)) (heta : IsState eta)
    (p : K → ℝ) (hp : ∀ k, 0 ≤ p k) (htotal : HasSum p 1)
    (rho : K → Matrix (Fin d) (Fin d) ℂ) (hrho : ∀ k, IsDensityMatrix (rho k))
    (M : Y → Matrix (Fin e) (Fin e) ℂ) (hM : IsCountablePOVM M) :
    let avg := ∑' k, (p k : ℂ) • rho k
    let Phi := dilationChannel U eta
    let P := fun z : K × Y => p z.1 * effectProb (M z.2) (environmentOutput U eta (rho z.1))
    Summable (fun k => (p k : ℂ) • rho k) ∧
    Summable (fun k => p k * entropyExchange Phi (rho k)) ∧
    jointInformation P ≤ ENNReal.ofReal (entropyExchange Phi avg -
      ∑' k, p k * entropyExchange Phi (rho k)) ∧
    entropyExchange Phi avg - (∑' k, p k * entropyExchange Phi (rho k)) =
      vnEntropy (environmentOutput U eta avg) -
        ∑' k, p k * vnEntropy (environmentOutput U eta (rho k)) ∧
    entropyExchange Phi avg - (∑' k, p k * entropyExchange Phi (rho k)) ≤
      entropyExchange Phi avg := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
