-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_corollary_3_4
-- name    : QuantumAdviceAmplification.Separation.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:04:58.607949+00:00
-- url     : https://prove2.me/theorems/fd73f67f-f361-49cc-ad78-dded9bc904eb
-- title:
--   Corollary 3.4 — Expected normalized covering distance
-- statement:
--   For every radius $0\le r\le\ell$, let $D(C)$ be the average distance of a uniform word to the nonempty code $C$, divided by $\ell$. Then
--   $$\mathbb E_tD(C_{T(t)})\le\frac r\ell+\frac{2^q}{V(\ell,r)}.$$
--   The left side uses the actual random code and an attained nearest-codeword distance.
--
--   Differences from the source:
--   - encoding: F2 vectors with one-based coordinates, ell>=2 and 1<=d<=ell-1 → Bool coordinates with ZMod 2 arithmetic, zero-based Fin indices, and positive d,q with ell=q+d; reason: the Boolean/field and coordinate bijections preserve the source code and all parameter choices
--   - encoding: probabilities and expectations over independent uniform finite choices → normalized finite sums and a uniform PMF on the product seed space; reason: the product law is exactly independent uniform sampling; every index space used here is nonempty
--   - encoding: distance is the minimum over the nonempty finite code → distance to the word computed by exhaustive rank-order nearest search; reason: the finite search attains the same minimum and resolves ties lexicographically
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.9, Corollary 3.4

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem corollary_3_4 (S : BlockShape) (r : ℕ) (hr : r ≤ S.ell) :
    epsilonStar S ≤ (r : ℝ) / S.ell + (2 : ℝ) ^ S.q / volume S.ell r := by sorry

end QuantumAdviceAmplification.Separation
