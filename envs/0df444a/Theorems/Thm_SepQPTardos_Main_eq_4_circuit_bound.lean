-- Prove2me | Theorems.Thm_SepQPTardos_Main_eq_4_circuit_bound
-- name    : SepQPTardos.Main.eq_4_circuit_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:03.693742+00:00
-- url     : https://prove2.me/theorems/5a7d4114-2705-4786-ab8e-19ee7623a4e0
-- title:
--   §2.1, eq. (4) — primitive integer circuits have entries bounded by $G=(rU)^r$
-- statement:
--   Let $A$ be an integer $r\times m$ matrix, $U=\max(1,\max_{i,e}|A_{ie}|)$ and $G=(rU)^r$. Then:
--
--   1. every circuit $v$ of $A$ (a nonzero kernel vector of inclusion-minimal support) is a nonzero real multiple $v=\mu h$ of a primitive integer vector $h$;
--   2. every primitive integer vector $h$ that is a circuit of $A$ satisfies
--   $$1\le|h_e|\le G\qquad(e\in\operatorname{supp}h).\tag{4}$$
--
--   Since the primitive representative of a circuit is unique up to sign, every circuit has a representative satisfying (4). The bound is what makes the coefficients of the conformal decompositions in Lemmas 3.2, 4.1 and 4.2 structurally bounded.
--
--   Differences from the source:
--   - generalization: every circuit of A has a representative h with 1 ≤ |h_e| ≤ G → every circuit is a multiple of a primitive integer vector, and every primitive integer circuit satisfies 1 ≤ |h_e| ≤ G; reason: the primitive representative is unique up to sign, so this implies the source's claim; Lemmas 3.2, 4.1, 4.2 apply (4) to primitive circuits
--   - generalization: r ≥ 1 and A of full row rank (assumed from §2.1 on) → every r ≥ 0 and every integer matrix A; reason: G = (rU)^r bounds the circuits of any integer matrix; at r = 0 the circuits are multiples of unit vectors and G = 1
--   - reading: In particular, log G = O(r log(rU)) → not restated; reason: it is the identity log G = r log(rU) of the definition G = (rU)^r
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §2.1, eq. (4), p. 4

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Circuits

namespace SepQPTardos.Main

/-- §2.1, eq. (4) (Cui–Li–Miao, STOC 2027 #829, p. 4): every circuit of an integer matrix `A`
is a nonzero multiple of a primitive integer vector, and every primitive integer circuit `h`
of `A` satisfies `1 ≤ |hₑ| ≤ G = (rU)^r` on its support. -/
theorem eq_4_circuit_bound {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) :
    (∀ v : Fin m → ℝ, IsCircuit (castMat A) v →
      ∃ h : Fin m → ℤ, Primitive h ∧ ∃ μ : ℝ, μ ≠ 0 ∧ v = μ • castIntVec h) ∧
    (∀ h : Fin m → ℤ, Primitive h → IsCircuit (castMat A) (castIntVec h) →
      ∀ e, h e ≠ 0 → 1 ≤ (h e).natAbs ∧ (h e).natAbs ≤ Gbound A) := by sorry

end SepQPTardos.Main
