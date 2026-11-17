-- Prove2me | Theorems.Thm_QuantumLTF_Majority_intersectionIndex_fiber_card
-- name    : QuantumLTF.Majority.intersectionIndex_fiber_card
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T00:49:59.463391+00:00
-- url     : https://prove2.me/theorems/6acb764e-e7e5-4456-991c-25c3f87c1101
-- title:
--   Cardinality of a support-intersection fiber
-- statement:
--   If $A\subseteq[n]$ has size $r$, then for every $0\le a\le r$, the number of Boolean strings $S$ satisfying $|A\cap S|=a$ is
--
--   $$
--   2^{n-r}{r\choose a}.
--   $$
--
--   Choose the $a$ selected coordinates inside $A$ and assign the remaining $n-r$ coordinates arbitrarily.
-- source:
--   Elementary Boolean-cube intersection counting used in the Section 4.2 adversary objective calculation of Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem intersectionIndex_fiber_card : ∀ n r : ℕ, r ≤ n → ∀ A : ExactSupports n r, ∀ a : Fin (r+1), (Finset.univ.filter fun S : Qubits n => intersectionIndex A S = a).card = 2^(n-r) * r.choose a := by sorry

end QuantumLTF.Majority
