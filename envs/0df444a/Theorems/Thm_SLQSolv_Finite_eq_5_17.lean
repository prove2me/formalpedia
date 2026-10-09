-- Prove2me | Theorems.Thm_SLQSolv_Finite_eq_5_17
-- name    : SLQSolv.Finite.eq_5_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:17.582149+00:00
-- url     : https://prove2.me/theorems/02ae4c42-c60e-469a-bb3a-5f343d4e9d7e
-- title:
--   (5.15) and (5.17), pp. 2296–2297 — P(0) ⩽ P_ε(0), and J⁰(t, x; u) ⩾ ⟨N(t)x, x⟩ for all (t, x) and u
-- statement:
--   Let (H1)–(H2) and (5.6) hold, for every $\varepsilon>0$ let $P_\varepsilon$ be the strongly regular solution of (5.7), let $M_0$ solve the Lyapunov equation (3.2) and $\Phi_A$ solve (5.12). Let $P(0)\in\mathbb S^n$ satisfy $V^0(0,x)=\langle P(0)x,x\rangle$ for all $x\in\mathbb R^n$, and let
--
--   $$
--   N(t)=\big[\Phi_A(t)^\top\big]^{-1}\Big\{P(0)-\int_0^t\Phi_A(s)^\top\big[C(s)^\top M_0(s)C(s)+Q(s)\big]\Phi_A(s)\,ds\Big\}\Phi_A(t)^{-1}.
--   $$
--
--   Then (5.15) $P(0)\le P_\varepsilon(0)$ for all $\varepsilon>0$, and (5.17)
--
--   $$
--   J^0(t,x;u)\ \ge\ \langle N(t)x,x\rangle\qquad\forall (t,x)\in[0,T]\times\mathbb R^n,\ \forall u\in\mathcal U[t,T].
--   $$
--
--   In particular Problem (SLQ)$^0$ is finite: this is how the sufficiency part of Theorem 5.3 passes from finiteness at $t=0$ to finiteness on all of $[0,T]$.
--
--   **Formalization Note** The page assumes this paragraph in the setting where $V^0(0,\cdot)$ is already finite; that is implied by the representation hypothesis on $P(0)$ and is not added separately. $\Phi_A(t)$ is invertible, so `⁻¹` is the true inverse. The first inequality is in the Loewner order.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §5, proof of Theorem 5.3 (Sufficiency), (5.15), p. 2296, and (5.17), p. 2297

import Mathlib
import Definitions.Def_SLQSolv_Finite_Comparison

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.Finite

theorem eq_5_17 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d) (h56 : IsNonnegJ0 Bs d 0)
    (Pε : ℝ → ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hPε : ∀ ε > 0, IsStronglyRegular (d.addR ε) (Pε ε))
    (M0 : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hM0 : IsLyapunovSol d 0 M0)
    (ΦA : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hΦ : IsFundSolA d ΦA)
    (P0 : Matrix (Fin n) (Fin n) ℝ) (hP0symm : P0.IsSymm)
    (hP0 : ∀ x, V0 Bs d 0 x = (((P0 *ᵥ x) ⬝ᵥ x : ℝ) : EReal)) :
    (∀ ε > 0, (Pε ε 0 - P0).PosSemidef) ∧
    ∀ t ≤ d.T, ∀ (x : Fin n → ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ), Adm Bs d t u →
      (nMat d M0 ΦA (fun _ => P0) t *ᵥ x) ⬝ᵥ x ≤ J0 Bs d t x u := by sorry

end SLQSolv.Finite
