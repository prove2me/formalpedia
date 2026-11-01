-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P08_proposition3
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P08.proposition3
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:26:09.257165+00:00
-- url     : https://prove2.me/theorems/1403461f-7f3c-4362-8306-9e313f34efcf
-- title:
--   Local one-cocycles are globally continuous
-- statement:
--   Let $G$ be a topological group and $A$ an abelian topological group with a continuous $G$-action by automorphisms. Let $Z_{\rm lcm}^1(G,A)$ consist of all everywhere-defined Borel maps $c:G\to A$ continuous on some open identity neighborhood and satisfying the pointwise crossed identity. Then
--   $$
--   Z_{\rm lcm}^1(G,A)=\{c:G\to A:\ c\text{ is continuous and }c(st)=c(s)+s\cdot c(t)\text{ for all }s,t\in G\}=Z_{\rm cont}^1(G,A).
--   $$
--   This identifies cocycles themselves; no quotient by principal crossed homomorphisms is taken.
-- source:
--   On Cohomology theory for topological groups, arXiv:1009.4519v1, PDF p. 11, Proposition 3: local one-cocycles are globally continuous

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P08

namespace QAlgorithms.Papers.Independent.Intakethird100.P08

open Set MeasureTheory

open scoped BigOperators Topology CompactlySupported

section DegreeOne

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace A] [BorelSpace A]

/-- Proposition 3, PDF p. 11: local one-cocycles are globally continuous.
No local compactness, countability, or trivial action is assumed. -/
theorem proposition3 (rho : ContinuousModule G A) :
    locallyContinuousOneCocycles rho = continuousOneCocycles rho := by sorry

end DegreeOne

end QAlgorithms.Papers.Independent.Intakethird100.P08
