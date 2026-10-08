-- Prove2me | Theorems.Thm_PacketRouting_CongDil_lemma_3_5
-- name    : PacketRouting.CongDil.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:02:27.934754+00:00
-- url     : https://prove2.me/theorems/07baf291-255c-4e2b-a8af-d3a8e8873b11
-- title:
--   Lemma 3.5, p. 14 — at most Ry packets on g in every y-frame for T ≤ y ≤ 2T − 1 implies the same for all y ≥ T
-- statement:
--   Fix any schedule of a finite set of packets (valid or not), an edge $g$, a real number $R$ and a frame size $T\ge 1$. For a frame of $y$ consecutive steps starting at step $t$, let $C_g(t,y)$ be the number of packets that cross $g$ at some step of the frame.
--
--   **Lemma 3.5.** If
--   $$
--   C_g(t,y)\le R\,y\qquad\text{for every start } t \text{ and every } y \text{ with } T\le y\le 2T-1,
--   $$
--   then $C_g(t,y)\le R\,y$ for every start $t$ and every $y\ge T$.
--
--   The lemma reduces the frame-congestion bounds of the refinement step to frames of a bounded range of sizes; it is used several times in the proof of Theorem 3.4.
--
--   **Formalization Note** The hypothesis $T\ge1$ is implicit on the page: for $T=0$ the range $T\le y\le 2T-1$ is empty and the conclusion fails. The range is written $T\le y<2T$.
-- source:
--   Leighton, Maggs & Rao, Packet routing and job-shop scheduling in O(congestion + dilation) steps, authors' manuscript (preprint of Combinatorica 14 (1994), DOI 10.1007/BF01215349), p. 14, Lemma 3.5

import Mathlib
import Definitions.Def_PacketRouting_CongDil_Timetable

namespace PacketRouting.CongDil

/-- Lemma 3.5 (Leighton–Maggs–Rao, p. 14): in any schedule (valid or not), if for every `y`
with `T ≤ y ≤ 2T − 1` at most `R y` packets use edge `g` in every `y`-frame, then at most `R y`
packets use `g` in every `y`-frame for every `y ≥ T`. -/
theorem lemma_3_5 {P E : Type*} [Fintype P] {path : P → List E} (τ : Timetable path)
    (g : E) (R : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (h : ∀ y t : ℕ, T ≤ y → y < 2 * T → (τ.frameCount g t y : ℝ) ≤ R * y) :
    ∀ y t : ℕ, T ≤ y → (τ.frameCount g t y : ℝ) ≤ R * y := by sorry

end PacketRouting.CongDil
