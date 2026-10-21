-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_proposition2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.proposition2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:33:49.882981+00:00
-- url     : https://prove2.me/theorems/8ca0bc08-2f13-4c56-8efb-779c1a39541f
-- title:
--   Proposition 2: local conditioning and local CPTP monotonicity
-- statement:
--   For any normalized state on finite nonzero registers, any $m\ge2$, and either $F=I_m$ or $F=S_m$, local conditioning and local quantum operations cannot increase the indicated information:
--
--   $$F(XA_1:A_2:\cdots:A_m)\ge F(A_1:\cdots:A_m\mid X),$$
--   $$F(A_1:\cdots:A_m\mid E)\ge F(\Lambda(A_1):A_2:\cdots:A_m\mid E).$$
--
--   Here $\Lambda$ is any trace-preserving completely positive map, including a map to a different finite nonzero output dimension; the other registers, including all coherences in $E$, remain untouched. These are the two monotonicity properties used for squashing.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 4, Proposition 2: local conditioning and local CPTP monotonicity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 2, PDF p.4,(22),(23): local conditioning and local CPTP
monotonicity of BOTH quantities, including dimension-changing maps. -/
theorem proposition2 {n k : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) (a : Fin (k+2) → Finset (Fin n))
    (x : Finset (Fin n)) (hdis : DisjointRegisters a x) :
    (∀ kind : InformationKind, info kind rho a x ≤
      info kind rho (attachFirst a x) ∅) ∧
    (∀ (m : ℕ) (D F : Fin m → Type) [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
      [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
      (E : Type) [Fintype E] [Nonempty E] (p : Fin m)
      (other : ∀ j, j ≠ p → D j ≃ F j) (Phi : Superop (D p) (F p))
      (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ),
      2 ≤ m → IsChannel Phi → IsDensityMatrix r → ∀ kind : InformationKind,
      conditionalMultipartiteInformation kind (localAction p other Phi r) (singleParties m) ∅ ≤
        conditionalMultipartiteInformation kind r (singleParties m) ∅) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
