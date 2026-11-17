-- Prove2me | Theorems.Thm_QuantumLTF_Majority_krawtchouk_parseval
-- name    : QuantumLTF.Majority.krawtchouk_parseval
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T00:28:58.297498+00:00
-- url     : https://prove2.me/theorems/8b6e93a5-19a6-436d-a8e3-ac3dbb6bb444
-- title:
--   Weighted Parseval identity for the Krawtchouk transform
-- statement:
--   For arbitrary real coefficients $r_0,\ldots,r_k$, the binary Krawtchouk transform satisfies
--
--   $$
--   2^{-k}\sum_{a=0}^k{k\choose a}\left(\sum_{t=0}^kK_t(a)r_t\right)^2=\sum_{t=0}^k{k\choose t}r_t^2.
--   $$
--
--   This is the weighted Parseval identity obtained directly from Krawtchouk orthogonality. It is reusable for both scalar and direct-sum adversary constructions.
-- source:
--   Standard consequence of weighted binary Krawtchouk orthogonality; used in Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

theorem krawtchouk_parseval : ∀ k : ℕ, ∀ r : Fin (k+1) → ℝ, (1/(2:ℝ)^k) * ∑ a : Fin (k+1), (k.choose a : ℝ) * (∑ t : Fin (k+1), (krawtchouk k t a : ℝ) * r t)^2 = ∑ t : Fin (k+1), (k.choose t : ℝ) * r t^2 := by sorry

end QuantumLTF.Majority
