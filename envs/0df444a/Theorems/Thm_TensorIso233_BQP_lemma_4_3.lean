-- Prove2me | Theorems.Thm_TensorIso233_BQP_lemma_4_3
-- name    : TensorIso233.BQP.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:27.042776+00:00
-- url     : https://prove2.me/theorems/58bddc56-7719-45db-83c6-a9151d3ceebd
-- title:
--   Lemma 4.3 — strict equivalence as an integral commuting square
-- statement:
--   Let $T=(A,B)$ and $T'=(A',B')$ have the same determinant form, $f_T=f_{T'}$, and suppose the common replacement (4.1) has been made, so that $\det A\neq0$ (hence $f_T\neq0$ and $\det A'=\det A$). Let $D=A^{-1}B$, $D'=A'^{-1}B'$, $E=BA^{-1}$, $E'=B'A'^{-1}$ over $\mathbb Q$ (4.4). Then:
--
--   1. $T\sim_{\mathrm{str}}T'$ if and only if there are $P,Q\in GL_3(\mathbb Z)$ with (4.7)
--   $$
--   PA=A'Q,\qquad QD=D'Q;
--   $$
--   2. equivalently, if and only if there are $P,Q\in GL_3(\mathbb Z)$ with $PA=A'Q$, $QD=D'Q$ and $PE=E'P$.
--
--   The second form records that the square (4.6) consists of module isomorphisms on both $N$ (where $\theta$ acts by $D$) and $L$ (where $\theta$ acts by $E$).
--
--   Differences from the source:
--   - reading: integral module isomorphisms Q : N → N′ and P : L → L′ making the square (4.6) commute → matrices Q, P ∈ GL₃(ℤ) in the integral bases with PA = A′Q, commuting with the θ-actions (QD = D′Q and PE = E′P); reason: Wood's modules N, L are not formalized; the lemma's own 'Equivalently' gives (4.7), and the proof identifies the module condition on L with PE = E′P
--   - encoding: same nonzero determinant form and the common replacement (4.1) has been made → detForm T = detForm T′ and det A ≠ 0; reason: (4.1) arranges f(1,0) = det A ≠ 0; this implies f_T ≠ 0 and det A′ = det A, so the stated nonzero-form hypothesis is implied and not repeated
-- source:
--   Thomas Huffstutler, Integral 2 × 3 × 3 Tensor Isomorphism is in BQP, STOC 2027 submission #319 (October 2026), Lemma 4.3, p. 16, (4.6)–(4.7); (4.1), p. 14; (4.4), p. 15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/319.pdf

import Definitions.Def_TensorIso233_BQP_Tensor

namespace TensorIso233.BQP

/-- Lemma 4.3 (p. 16): for `T, T'` with the same determinant form after the replacement (4.1)
(so `det A = det A' ≠ 0`), `T ∼str T'` iff there are `P, Q ∈ GL₃(ℤ)` with `PA = A'Q` and
`QD = D'Q` (4.7); equivalently, together with the module condition `PE = E'P` on `L`. -/
theorem lemma_4_3 (T T' : Tensor) (hf : detForm T = detForm T') (hA : T.1.det ≠ 0) :
    (StrictEquiv T T' ↔
      ∃ P Q : GL3, (P : Mat3) * T.1 = T'.1 * (Q : Mat3) ∧
        toQ (Q : Mat3) * opD T = opD T' * toQ (Q : Mat3)) ∧
    (StrictEquiv T T' ↔
      ∃ P Q : GL3, (P : Mat3) * T.1 = T'.1 * (Q : Mat3) ∧
        toQ (Q : Mat3) * opD T = opD T' * toQ (Q : Mat3) ∧
        toQ (P : Mat3) * opE T = opE T' * toQ (P : Mat3)) := by sorry

end TensorIso233.BQP
