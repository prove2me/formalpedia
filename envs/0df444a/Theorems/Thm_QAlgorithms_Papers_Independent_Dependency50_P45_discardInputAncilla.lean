-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_discardInputAncilla
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.discardInputAncilla
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:04:58.847278+00:00
-- url     : https://prove2.me/theorems/acea2c4a-a245-49d4-86a1-e883ce04b306
-- title:
--   Lemma 2: discarding an input ancilla cannot increase maximum mutual information
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP map, with $A,B$ nonzero finite-dimensional complex spaces, and let $K$ be any finite nonzero ancillary input space. Construct $\mathcal N'(\rho')=\mathcal N(\operatorname{Tr}_K\rho')$. For a channel $\mathcal M$, write $I(\rho,\mathcal M)=H(\rho)+H(\mathcal M(\rho))-H((\operatorname{id}\otimes\mathcal M)\Phi_\rho)$, where $\Phi_\rho$ is a normalized purification and entropies are in bits. Then
--
--   $$\max_{\rho'\text{ density on }A\otimes K}I(\rho',\mathcal N')\le\max_{\rho\text{ density on }A}I(\rho,\mathcal N).$$
--
--   The maxima are over all density matrices; the result does not restrict encoding operations to unitaries. This compares the full optimized objectives rather than only a pointwise proof inequality.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 23, Lemma 2: discarding an input ancilla cannot increase maximum mutual information

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF pp.23--24, Lemma 2: trace out the ancilla before N, and compare maxima. -/
theorem discardInputAncilla {A B K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [DecidableEq K]
    [Nonempty A] [Nonempty B] [Nonempty K] (N : Superop A B) (hN : IsChannel N) :
    maximalMutualInfo (fun rho : Matrix (A × K) (A × K) ℂ => N (traceRight rho)) ≤
      maximalMutualInfo N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
