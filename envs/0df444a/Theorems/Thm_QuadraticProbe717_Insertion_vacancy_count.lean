-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_vacancy_count
-- name    : QuadraticProbe717.Insertion.vacancy_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:57.720396+00:00
-- url     : https://prove2.me/theorems/a5324476-96e8-418d-9725-11fb68f472d2
-- title:
--   Equation (2) — exact vacancy count
-- statement:
--   For every fixed hash list of length $r$, apply the insertion process to the empty table of size $n>0$. Its number $Z$ of vacant slots satisfies
--   $$Z=(n-r)_+.$$
--   The identity holds for each realization, including lists with $r\ge n$. It therefore also gives the source's Poissonized identity when $r=N$ is sampled from the Poisson law.
--
--   Differences from the source:
--   - encoding: Z=(n−N)₊ in the Poissonized experiment → n minus the occupied-set cardinality equals natural subtraction n−r for every hash list; reason: natural subtraction is precisely the nonnegative part here; the identity is pointwise in the sampled hashes
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), equation (2), p. 6 (PDF p. 6)

import Definitions.Def_QuadraticProbe717_Insertion_laws

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem vacancy_count (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (hashes : List (ZMod n)) :
    vacantCount n (occupied n π hashes) = n - hashes.length := by sorry

end QuadraticProbe717.Insertion
