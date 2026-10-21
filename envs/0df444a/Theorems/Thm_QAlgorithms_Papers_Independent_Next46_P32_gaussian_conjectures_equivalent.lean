-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P32_gaussian_conjectures_equivalent
-- name    : QAlgorithms.Papers.Independent.Next46.P32.gaussian_conjectures_equivalent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:33:54.213626+00:00
-- url     : https://prove2.me/theorems/789416ab-c318-41f2-8dcb-56bd30fd8b9d
-- title:
--   Equivalence of globally quantified Gaussian entropy conjectures
-- statement:
--   For every $n\ge1$, $0\le\eta\le1$ and $K\ge0$, consider independent input ports and output $c=\sqrt\eta\,a+\sqrt{1-\eta}\,b$. All states are normalized positive trace-class full-Fock densities; Gaussian states may have arbitrary displacements and correlations within each port. Put $m=n g((1-\eta)K)$, where $g(x)=(x+1)\ln(x+1)-x\ln x$.
--
--   Let $\mathsf G_1$ be the globally quantified assertion that, with $b$ fixed to $n$ identical thermal states of mean $K$, every Gaussian $a$ input has output von Neumann entropy at least $m$, attained by vacuum $a$. Let $\mathsf G_2$ be the globally quantified assertion that, with $a$ in vacuum, every Gaussian $b$ input with entropy $ng(K)$ has output entropy at least $m$, attained by the identical thermal product input (whose entropy is $ng(K)$). Then
--
--   $$
--   \mathsf G_1\quad\Longleftrightarrow\quad\mathsf G_2.
--   $$
--
--   The quantification over all parameter triples is part of both predicates; this is not a claim that one triple implies every other triple. This equivalence transfers Gaussian minimum-entropy results between the two optimization problems.
-- source:
--   Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture, arXiv:0706.3416v1, PDF p. 10, Appendix A.2, Theorem 1; PDF pp.9-11

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity productCoeff)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Appendix A.2, Theorem 1, PDF pp.9-11 (Theorem 1 on p.10): both globally
quantified Gaussian conjectures are equivalent, with arbitrary displacements.
Correction: p.11 (A29)-(A31) and following prose print sqrt(1-eta) multiplying
photon occupation; changed to intensity 1-eta, required by (A25), p.8 Strong
Conjecture 2, and the thermal transformation. Strong Conjecture 1 uses identical
thermal occupations, as the reverse implication explicitly specifies on p.11. -/
theorem gaussian_conjectures_equivalent :
    GaussianStrongConjecture1 ↔ GaussianStrongConjecture2 := by sorry

end QAlgorithms.Papers.Independent.Next46.P32

end
