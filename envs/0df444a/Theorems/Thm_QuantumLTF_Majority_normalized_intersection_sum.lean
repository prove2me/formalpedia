-- Prove2me | Theorems.Thm_QuantumLTF_Majority_normalized_intersection_sum
-- name    : QuantumLTF.Majority.normalized_intersection_sum
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T00:42:11.403309+00:00
-- url     : https://prove2.me/theorems/f8753172-8aff-41c0-b1a1-ee889b35e3eb
-- title:
--   Normalized counting by support-intersection size
-- statement:
--   Let $A\subseteq[n]$ have cardinality $r$. For any real function $f$ of the intersection size, averaging uniformly over Boolean query strings gives the binomial distribution:
--
--   $$
--   2^{-n}\sum_{S\subseteq[n]}f(|A\cap S|)=2^{-r}\sum_{a=0}^r{r\choose a}f(a).
--   $$
--
--   Indeed, for each fixed $a$, there are ${r\choose a}$ choices inside $A$ and $2^{n-r}$ unrestricted choices outside $A$. This identity converts the dual matrix’s diagonal sum into the weighted Krawtchouk norm.
-- source:
--   Elementary Hamming-slice counting used in the diagonal objective calculation of Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem normalized_intersection_sum : ∀ n r : ℕ, r ≤ n → ∀ A : ExactSupports n r, ∀ f : Fin (r+1) → ℝ, (2 : ℝ)^(-n : ℤ) * ∑ S : Qubits n, f (intersectionIndex A S) = (1/(2:ℝ)^r) * ∑ a : Fin (r+1), (r.choose a : ℝ) * f a := by sorry

end QuantumLTF.Majority
