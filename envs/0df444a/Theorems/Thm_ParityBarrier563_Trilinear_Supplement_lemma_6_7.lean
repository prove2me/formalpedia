-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_lemma_6_7
-- name    : ParityBarrier563.Trilinear.Supplement.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:46:53.58235+00:00
-- url     : https://prove2.me/theorems/2faf08b8-9ab4-4df5-ba3a-709265bebb87
-- title:
--   Lemma 6.7 — Inverse-trace bound on every restricted small-bottom-fan-in circuit
-- statement:
--   For every integer $d\ge3$ there exist $a_d,c_d>0$ and $N_d\ge2$ such that for every $n\ge N_d$, every basis of $\mathbb F_{2^n}$ and $n\le s\le2^{a_dn^{1/(d-1)}}$, the following holds. Let τ fix at most n/4 coordinates and let C be a layered depth-d circuit of size at most s whose bottom fan-in after τ is at most $3\log_2(4s)$. For the inverse-trace sign g,
--   $$|\mathbb E[g_\tau C_\tau]|\le2^{-c_d n\log_2\log_2 s/(\log_2 s)^{d-1}}.$$
--   Constants and threshold depend only on d, uniformly in the basis, s and every fixed value of τ. This supplies the restricted circuit correlation estimate for Theorem 1.3.
--
--   Differences from the source:
--   - encoding: Ω_d bound and sufficiently large n → positive constants and a threshold preceding the basis,s,τ,C; reason: these quantify the printed asymptotics with dependence only on d
--   - encoding: the field of order 2^n in every binary basis → an arbitrary field K with an F₂-algebra structure and an n-vector basis; reason: the basis bijects K with F₂^n and enforces order 2^n without any additional restriction
--   - encoding: alternating layered circuits, with actual gate count and the stated fan-in bounds → Layering data over the published Circuit DAG, retaining constants and unary gates and counting literal or gate wires; reason: this is the source layer convention and keeps both output types; duplicate wires can be deleted without increasing any bound
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Lemma 6.7, printed p.30 / PDF p.32

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_InverseTrace
import Definitions.Def_ParityBarrier563_Trilinear_Supplement_Layering

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Lemma 6.7, including the full size interval and every fixed value of τ. -/
theorem lemma_6_7 (d : ℕ) (hd : 3 ≤ d) :
  ∃ (a c : ℝ) (N : ℕ), 0 < a ∧ 0 < c ∧ 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ (K : Type) [Field K] [Algebra (ZMod 2) K]
      (e : Module.Basis (Fin n) (ZMod 2) K) (s : ℝ),
    (n : ℝ) ≤ s → s ≤ (2 : ℝ)^(a*(n : ℝ)^(1/((d : ℝ)-1))) →
    ∀ (τ : Restriction (Fin n)), (fixedCount τ : ℝ) ≤ (n : ℝ)/4 →
    ∀ (C : Circuit (Fin n)) (L : Layering C d), (C.size : ℝ) ≤ s →
      BottomBound L τ (3*Real.logb 2 (4*s)) →
    |avg (fun z => restrict τ (sgn (inverseTrace e)) z * ind (restrict τ C.eval) z)| ≤
      (2 : ℝ)^(-c*averageExponent d n s) := by sorry

end ParityBarrier563.Trilinear.Supplement
