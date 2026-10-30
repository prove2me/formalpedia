-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P05_decodingFromDecoupling
-- name    : QAlgorithms.Papers.Independent.Advance50.P05.decodingFromDecoupling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:27:24.908994+00:00
-- url     : https://prove2.me/theorems/97a5627e-541f-4849-a08d-31a9a69f55e8
-- title:
--   Decoding from decoupling for an arbitrary pure vector
-- statement:
--   Let $H_{A'},H_B,H_E,H_{B'}$ be positive-dimensional finite Hilbert spaces, and let $|\Omega\rangle\in H_{A'}\otimes H_B\otimes H_E$ have arbitrary norm, including zero. Write $\omega^{A'B}$ and $\omega^{A'E}$ for the corresponding partial traces of $|\Omega\rangle\langle\Omega|$. Fix a normalized state $\chi^E$ and a normalized maximally entangled state $\Psi_m^{A'B'}$ of positive integer rank $m\le\min(\dim H_{A'},\dim H_{B'})$. Set $\tau^{A'}=\operatorname{Tr}_{B'}\Psi_m$. There exists a CPTP decoder $\mathcal D:B\to B'$ such that
--   $$
--   F\bigl((\mathrm{id}_{A'}\otimes\mathcal D)(\omega^{A'B}),\Psi_m^{A'B'}\bigr)^2\ge F\bigl(\omega^{A'E},\tau^{A'}\otimes\chi^E\bigr)^2.
--   $$
--   Here $F(P,Q)=\operatorname{Tr}\sqrt{\sqrt P Q\sqrt P}$ is root fidelity for positive operators, without any added vacuum term. Both the target and $\chi^E$ are fixed before the decoder is chosen. The same statement holds for normalized and unnormalized $|\Omega\rangle$.
--
--   The lemma converts decoupling of the environment into a physical decoding guarantee. **Formalization Note:** orthonormal local frames construct the fixed target, and both complementary states are computed from the same vector.
-- source:
--   Distilling entanglement from arbitrary resources, arXiv:1006.1896v2, PDF p. 16, Lemma 10, Eq.(60): decoding from decoupling

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P05

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P19 (first both epr IsIso)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Support50.P21 (dMin weakPositive PositiveTensorBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Buscemi--Datta, arXiv:1006.1896v2, PDF p.16, Lemma 10, (60).
The target frames and normalized chi are fixed before choosing the CPTP decoder.
Omega has arbitrary norm, including zero. Both sides are SQUARED root fidelity. -/
theorem decodingFromDecoupling
    {A B E D : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    [Fintype D] [DecidableEq D] [Nonempty D]
    (omega : EuclideanSpace ℂ (A × (B × E)))
    (chi : Matrix E E ℂ) (hchi : IsDensityMatrix chi)
    (m : ℕ) (hm : 0 < m)
    (U : Matrix A (Fin m) ℂ) (V : Matrix D (Fin m) ℂ)
    (hU : IsIso U) (hV : IsIso V) :
    ∃ decoder : Superop B D, IsChannel decoder ∧
      rootFidelity (idTensorSuperop decoder (marginalAB (pureDensity omega))) (embeddedMES U V) ^ 2 ≥
        rootFidelity (marginalAC (pureDensity omega))
          (Matrix.kronecker (traceRight (embeddedMES U V)) chi) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P05

end
