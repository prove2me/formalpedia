-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_entanglementBreaking_equivalences
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.entanglementBreaking_equivalences
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:18:22.617641+00:00
-- url     : https://prove2.me/theorems/5bc68c69-28f6-44f3-9c14-51de11af7e7c
-- title:
--   Theorem 4(A)--(F), with trace-preserving specialization
-- statement:
--   Let $d\ge1$ and let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be complex-linear. Write $\beta=d^{-1/2}\sum_j|j,j\rangle$. The following six conditions are equivalent:
--
--   1. A finite Holevo form with density outputs and positive semidefinite effects exists.
--   2. $\Phi$ breaks entanglement in the separable positive cone.
--   3. Its normalized Choi operator $(\mathrm{id}\otimes\Phi)(|\beta\rangle\langle\beta|)$ is in that cone.
--   4. It has a finite operator-sum representation with every Kraus operator of rank exactly one.
--   5. $\Upsilon\circ\Phi$ is completely positive for every positivity-preserving complex-linear endomap $\Upsilon$ of $M_d$.
--   6. $\Phi\circ\Upsilon$ is completely positive for every such $\Upsilon$.
--
--   $$\mathrm{A}\Longleftrightarrow\mathrm{B}\Longleftrightarrow\mathrm{C}\Longleftrightarrow\mathrm{D}\Longleftrightarrow\mathrm{E}\Longleftrightarrow\mathrm{F}.$$
--
--   If $\Phi$ preserves trace, the corresponding six-way equivalence holds with a POVM in A, EBT in B, normalized separable density in C, $\sum_k A_k^\dagger A_k=I$ in D, and trace-preserving positivity tests in E,F. Empty general representations are allowed for the zero map. This supplies all the theorem's characterizations, including its continuation on page 5.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Theorem 4(A)--(F), with trace-preserving specialization, PDF p. 4. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02























































/-- Theorem 4(A)–(F), PDF pp.4–6. No CP or TP assumption in the general
equivalence. The TP specialization normalizes C,D and restricts the test maps
in E,F to trace-preserving ones. -/
theorem entanglementBreaking_equivalences (d : ℕ) (hd : 0 < d) (Phi : Endomorphism d) :
    List.TFAE [HasHolevoRepresentation Phi false,
      Entanglement.IsEntanglementBreakingPositive Phi,
      Entanglement.IsSeparablePositive (choiOperator hd Phi),
      HasRankOneRepresentation Phi false,
      ∀ Upsilon : Endomorphism d, PreservesPositive Upsilon →
        Entanglement.IsCompletelyPositive (Upsilon.comp Phi),
      ∀ Upsilon : Endomorphism d, PreservesPositive Upsilon →
        Entanglement.IsCompletelyPositive (Phi.comp Upsilon)] ∧
    (PreservesTrace Phi →
      letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
      List.TFAE [HasHolevoRepresentation Phi true, Phi ∈ ebtSet d,
        Entanglement.IsSeparableDensity (choiOperator hd Phi),
        HasRankOneRepresentation Phi true,
        ∀ Upsilon : Endomorphism d, PreservesPositive Upsilon → PreservesTrace Upsilon →
          Entanglement.IsCompletelyPositive (Upsilon.comp Phi),
        ∀ Upsilon : Endomorphism d, PreservesPositive Upsilon → PreservesTrace Upsilon →
          Entanglement.IsCompletelyPositive (Phi.comp Upsilon)]) := by sorry














end QAlgorithms.Papers.Independent.Independent1.P02
