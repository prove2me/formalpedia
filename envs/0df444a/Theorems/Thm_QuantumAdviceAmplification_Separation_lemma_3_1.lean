-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_lemma_3_1
-- name    : QuantumAdviceAmplification.Separation.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:04:47.445861+00:00
-- url     : https://prove2.me/theorems/3dfdef28-1703-442c-a967-fc0b0b465b11
-- title:
--   Lemma 3.1 — Toeplitz code as a kernel
-- statement:
--   For the systematic Toeplitz code $C_T=\{(u,Tu):u\in\mathbb F_2^d\}$ and $H_T=[T\mid I_q]$, every word $w\in\mathbb F_2^\ell$ satisfies
--   $$w\in C_T\quad\Longleftrightarrow\quad H_Tw=0.$$
--   This identifies the code with the kernel used in the syndrome-covering estimates.
--
--   Differences from the source:
--   - encoding: F2 vectors with one-based coordinates, ell>=2 and 1<=d<=ell-1 → Bool coordinates with ZMod 2 arithmetic, zero-based Fin indices, and positive d,q with ell=q+d; reason: the Boolean/field and coordinate bijections preserve the source code and all parameter choices
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.8, Lemma 3.1

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem lemma_3_1 (S : BlockShape) (t : Bits (S.ell - 1)) (w : Bits S.ell) :
    w ∈ toeplitzCode S t ↔ syndrome S t w = 0 := by sorry

end QuantumAdviceAmplification.Separation
