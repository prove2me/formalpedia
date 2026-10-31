-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma1_3_helstrom_invariant_full_rank
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma1_3_helstrom_invariant_full_rank
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:41:07.019996+00:00
-- url     : https://prove2.me/theorems/47cd3d9e-9071-46b8-b77e-f251d8c87e48
-- title:
--   Lemma 1.3: Helstrom supports invariant after transpose recovery
-- statement:
--   Let $\mathcal E$ be a CPTP map between finite-dimensional nonzero complex Hilbert spaces, and let $C$ be a convex set of positive matrices of ordinary trace one. Preservation means equality of $\|\mathcal E(p\rho-(1-p)\sigma)\|_1$ and $\|p\rho-(1-p)\sigma\|_1$ for every $\rho,\sigma\in C$ and $p\in[0,1]$. Assume $C$ is preserved and write $P=\operatorname{supp}C$, $\Delta=p\rho-(1-p)\sigma$ for $\rho,\sigma\in C$, $p\in[0,1]$. Let $P_\pm$ be the supports of the spectral positive and negative parts, and let $T=\widehat{\mathcal E}_P\circ\mathcal E$ be the computed support-transpose composite. Assume $\Delta$ has no kernel on $P$. Then
--
--   $$P_\pm X P_\pm=X\quad\Longrightarrow\quad P_\pm T(X)P_\pm=T(X)\qquad\text{for every operator }X.$$
--
--   The entire two-sided Helstrom corners are invariant.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 21, Lemma 1.3: Helstrom supports invariant after transpose recovery

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

/-- PDF p.21, Lemma 1.3. The rank hypothesis is relative to the support
of the entire convex code, not merely the support of Delta. -/
theorem lemma1_3_helstrom_invariant_full_rank {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Superop I J) (hE : IsChannel E) (C : Set (Op I)) (hC : IsCode C)
    (hPres : Preserved E C) (rho sigma : Op I) (hr : rho ∈ C) (hs : sigma ∈ C)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hRank : FullRankOn (codeSupport C) (weighted p rho sigma)) :
    CornerInvariant (transposeRecovery E (codeSupport C) ∘ E)
      (supportProjector (positivePart (weighted p rho sigma))) ∧
    CornerInvariant (transposeRecovery E (codeSupport C) ∘ E)
      (supportProjector (negativePart (weighted p rho sigma))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
