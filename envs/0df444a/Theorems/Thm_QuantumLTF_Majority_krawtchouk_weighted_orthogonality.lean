-- Prove2me | Theorems.Thm_QuantumLTF_Majority_krawtchouk_weighted_orthogonality
-- name    : QuantumLTF.Majority.krawtchouk_weighted_orthogonality
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-16T18:09:56.002804+00:00
-- url     : https://prove2.me/theorems/053c8b77-a2f6-4575-8cf7-0382d5a955fc
-- title:
--   Weighted orthogonality of binary Krawtchouk polynomials
-- statement:
--   For the binary Krawtchouk polynomials $K_t(a)$ on the Hamming cube of dimension $k$, the binomially weighted inner product satisfies
--
--   $$
--   \sum_{a=0}^{k}{k\choose a}K_t(a)K_u(a)=2^k{k\choose t}\,\mathbf 1_{t=u}.
--   $$
--
--   Thus the Krawtchouk transform is orthogonal after weighting its input and output coordinates by the binomial coefficients. This identity is the reusable harmonic-analysis step behind the corrected two-channel Parseval formula in Section 4.
-- source:
--   Standard binary Krawtchouk orthogonality; Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Section 4.2, orthogonality calculation used in Lemma 4.2.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

theorem krawtchouk_weighted_orthogonality : ∀ k : ℕ, ∀ t u : Fin (k+1), ∑ a : Fin (k+1), (k.choose a : ℝ) * (krawtchouk k t a : ℝ) * (krawtchouk k u a : ℝ) = if t = u then (2:ℝ)^k * (k.choose t : ℝ) else 0 := by sorry

end QuantumLTF.Majority
