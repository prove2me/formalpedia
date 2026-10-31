-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma1_4_helstrom_invariant
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma1_4_helstrom_invariant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:41:57.5206+00:00
-- url     : https://prove2.me/theorems/6b5f9f83-19b5-46a7-8b22-9fed14f3a555
-- title:
--   Lemma 1.4: Helstrom supports invariant after transpose recovery
-- statement:
--   Let $\mathcal E$ be a CPTP map between finite-dimensional nonzero complex Hilbert spaces, and let $C$ be a convex set of positive matrices of ordinary trace one. Preservation means equality of $\|\mathcal E(p\rho-(1-p)\sigma)\|_1$ and $\|p\rho-(1-p)\sigma\|_1$ for every $\rho,\sigma\in C$ and $p\in[0,1]$. Assume $C$ is preserved and write $P=\operatorname{supp}C$, $\Delta=p\rho-(1-p)\sigma$ for $\rho,\sigma\in C$, $p\in[0,1]$. Let $P_\pm$ be the supports of the spectral positive and negative parts, and let $T=\widehat{\mathcal E}_P\circ\mathcal E$ be the computed support-transpose composite. No rank hypothesis on $\Delta$ is required. Then
--
--   $$P_\pm X P_\pm=X\quad\Longrightarrow\quad P_\pm T(X)P_\pm=T(X)\qquad\text{for every operator }X.$$
--
--   The entire two-sided Helstrom corners are invariant.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 21, Lemma 1.4: Helstrom supports invariant after transpose recovery

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF p.21, Lemma 1.4: the same exact invariance without a rank hypothesis.
Delta=0 has zero positive and negative supports. -/
theorem lemma1_4_helstrom_invariant {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Superop I J) (hE : IsChannel E) (C : Set (Op I)) (hC : IsCode C)
    (hPres : Preserved E C) (rho sigma : Op I) (hr : rho ∈ C) (hs : sigma ∈ C)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    CornerInvariant (transposeRecovery E (codeSupport C) ∘ E)
      (supportProjector (positivePart (weighted p rho sigma))) ∧
    CornerInvariant (transposeRecovery E (codeSupport C) ∘ E)
      (supportProjector (negativePart (weighted p rho sigma))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
