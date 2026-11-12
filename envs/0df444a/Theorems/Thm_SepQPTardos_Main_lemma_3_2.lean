-- Prove2me | Theorems.Thm_SepQPTardos_Main_lemma_3_2
-- name    : SepQPTardos.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:23.671281+00:00
-- url     : https://prove2.me/theorems/7430a5d4-7aa2-4bd3-bf98-7d84501162b8
-- title:
--   Lemma 3.2 — two-sided continuous–integer proximity within $\ell_\infty$ distance $mG$
-- statement:
--   Let $A$ be an integer $r\times m$ matrix with $G=(rU)^r$ as in (3), let $\beta\in\mathbb R^r$ and $\ell,h\in\mathbb R^m$ (the bounds need not be integral), and put
--
--   $$P=\{u\in\mathbb R^m: Au=\beta,\ \ell\le u\le h\},$$
--
--   a bounded polyhedron; assume $P\cap\mathbb Z^m\ne\emptyset$. Let $\psi(u)=\sum_e(a_eu_e^2+b_eu_e)$ with $a\ge0$ be a separable convex quadratic. Then
--
--   1. for every minimiser $v$ of $\psi$ on $P$ there is a minimiser $w$ of $\psi$ on $P\cap\mathbb Z^m$ with $\|w-v\|_\infty\le mG$;
--   2. for every minimiser $w$ of $\psi$ on $P\cap\mathbb Z^m$ there is a minimiser $v$ of $\psi$ on $P$ with $\|w-v\|_\infty\le mG$.
--
--   This is the box version of the Hochbaum–Shanthikumar proximity theorem [HS90, Theorem 3.3]; the local solver uses both directions to pass from the compressed objective back to the original one through a common integer optimum.
--
--   Differences from the source:
--   - generalization: A the constraint matrix of (1) after §2.1 (full row rank, r ≥ 1) → any integer r × m matrix; reason: the proof uses only (4) and Lemma 2.1, valid for every integer matrix
--   - encoding: any separable convex quadratic ψ → ψ(u) = Σ_e (a_e u_e² + b_e u_e) with a ≥ 0; reason: an additive constant changes no minimiser
--   - encoding: P bounded → no hypothesis; reason: P lies in the box ℓ ≤ u ≤ h, so it is always bounded
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §3, Lemma 3.2, p. 6 (proof p. 7)

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Circuits
import Definitions.Def_SepQPTardos_Main_Analysis

namespace SepQPTardos.Main

/-- Lemma 3.2 (two-sided integer proximity; Cui–Li–Miao, STOC 2027 #829, p. 6): let
`P = {u : Au = β, ℓ ≤ u ≤ h}` with `A` an integer `r × m` matrix and real (not necessarily
integral) `β, ℓ, h`, and assume `P ∩ ℤ^m ≠ ∅`. For a separable convex quadratic
`ψ(u) = ∑ₑ (aₑuₑ² + bₑuₑ)`, `a ≥ 0`, every minimiser of `ψ` on `P` has a minimiser of `ψ` on
`P ∩ ℤ^m` within `ℓ∞` distance `mG`, and every minimiser on `P ∩ ℤ^m` has a minimiser on `P`
within `ℓ∞` distance `mG`. -/
theorem lemma_3_2 {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) (β : Fin r → ℝ) (ℓ hi : Fin m → ℝ)
    (a bl : Fin m → ℝ) (ha : ∀ e, 0 ≤ a e)
    (hint : ∃ w : Fin m → ℤ, castIntVec w ∈ boxPoly A β ℓ hi) :
    (∀ v, IsMinimizer (boxPoly A β ℓ hi) (sepQuad a bl) v →
      ∃ w : Fin m → ℤ,
        IsMinimizer {w : Fin m → ℤ | castIntVec w ∈ boxPoly A β ℓ hi}
          (fun w => sepQuad a bl (castIntVec w)) w ∧
        ∀ e, |(w e : ℝ) - v e| ≤ (m : ℝ) * (Gbound A : ℝ)) ∧
    (∀ w : Fin m → ℤ,
      IsMinimizer {w : Fin m → ℤ | castIntVec w ∈ boxPoly A β ℓ hi}
        (fun w => sepQuad a bl (castIntVec w)) w →
      ∃ v, IsMinimizer (boxPoly A β ℓ hi) (sepQuad a bl) v ∧
        ∀ e, |(w e : ℝ) - v e| ≤ (m : ℝ) * (Gbound A : ℝ)) := by sorry

end SepQPTardos.Main
