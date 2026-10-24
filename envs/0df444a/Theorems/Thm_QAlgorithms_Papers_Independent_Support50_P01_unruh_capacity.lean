-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_unruh_capacity
-- name    : QAlgorithms.Papers.Independent.Support50.P01.unruh_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:13:37.003107+00:00
-- url     : https://prove2.me/theorems/8799e86a-2f21-44f1-a974-82fb51ea2af4
-- title:
--   §III.B: full Unruh-channel capacity series
-- statement:
--   For $0<z<1$, let $\mathcal N_z$ be the full Unruh channel of Eqs.(11),(12), with receiver $\bigoplus_{k\ge0}\mathbb C^{k+2}$, genuine environment $\bigoplus_{k\ge0}\mathbb C^{k+1}$, and the common flagged dilation of the $1\to k+1$ cloning sectors with weights $p_k(z)=(1-z)^3z^k(k+1)(k+2)/2$. Use the entire countable sums, bit entropies, and unrestricted entangled density inputs for every positive block length. Write $Q(z)$ for the regularized optimized coherent information of this channel. Then
--   $$
--   Q(z)=I_c(\mathcal N_z,I_2/2)=\sum_{k=0}^{\infty}p_k(z)\big[\log_2(k+2)-\log_2(k+1)\big].
--   $$
--   The displayed series converges. Both full output entropy series converge for every normalized input to every positive finite block length $n$, and such an input $\rho$ satisfies $I_c(\mathcal N_z^{\otimes n},\rho)\le nI_c(\mathcal N_z,I_2/2)$. The normalized maximally mixed one-use input attains capacity. This evaluates the actual infinite-output channel rather than a cutoff approximation.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 7, §III.B: full Unruh-channel capacity series

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation quantumCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {a b e c : ℕ}

/-- PDF p.7, Eqs.(11)–(13): full capacity series, entropy convergence and optimizer.
The standard-polylogarithm equality printed afterwards is deferred for its missing
factor 1/log(2); the preceding series is used exactly with bit logarithms. -/
theorem unruh_capacity (z : ℝ) (hz0 : 0<z) (hz1 : z<1) :
    Summable (unruhSeriesTerm z) ∧
    (∀ n : ℕ, 0<n → ∀ rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
      IsDensityMatrix rho →
        Summable (fun ks => vnEntropy (unruhReceiverBlock z ks rho)) ∧
        Summable (fun ks => vnEntropy (unruhEnvironmentBlock z ks rho))) ∧
    IsDensityMatrix unruhMixedInput ∧
    unruhCapacity z = unruhCoherentInformation z unruhMixedInput ∧
    unruhCapacity z = ∑' k : ℕ, unruhSeriesTerm z k ∧
    (∀ n : ℕ, 0<n → ∀ rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
      IsDensityMatrix rho → unruhCoherentInformation z rho ≤
        (n : ℝ) * unruhCoherentInformation z unruhMixedInput) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
