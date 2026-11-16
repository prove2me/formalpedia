-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_proposition_5_10
-- name    : ParityBarrier563.Trilinear.Supplement.proposition_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:43:42.597347+00:00
-- url     : https://prove2.me/theorems/7c8217a9-eb13-482b-a81d-5bc188d272ed
-- title:
--   Proposition 5.10 — Inverse-trace correlation after restrictions, uniformly in the parameters
-- statement:
--   There exist absolute constants $c,M>0$ with the following property. Let $n\ge1$, choose any basis of $\mathbb F_{2^n}$ and let τ fix at most n/4 coordinates. Let integers $k\ge b\ge1$, $0<q\le1$, $p=b/(64k)$ and $m=qp|\operatorname{live}(\tau)|\ge M$. Suppose an integer $L\ge1$ satisfies $\log_2(8L)\le m/16$ and $mL\le n/64$. Suppose every b-CNF on every variable set V with $|V|\le2m$ is a sum of at most $2^{|V|/32}$ closures $\mathrm{cl}_b(S)$ with $|S|\le L$. For the sign g of inverse trace and a q-random restriction φ of live(τ),
--   $$\mathbb E_\varphi\operatorname{corr}_k(g_{\tau\varphi})\le2^{-cm}.$$
--   The constants are independent of the field, basis, fixed values, widths and all distribution parameters. This is the restricted inverse-trace correlation bound used by the companion lower bounds.
--
--   Differences from the source:
--   - encoding: every finite variable set of at most 2m coordinates and an absolute Ω bound → Fin t representatives and positive absolute c,M quantified first; reason: bijections preserve CNFs and closures; positive constants express the printed uniform asymptotic
--   - encoding: the field of order 2^n in every binary basis → an arbitrary field K with an F₂-algebra structure and an n-vector basis; reason: the basis bijects K with F₂^n and enforces order 2^n without any additional restriction
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Proposition 5.10, printed p.23 / PDF p.25

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_InverseTrace
import Definitions.Def_ParityBarrier563_Trilinear_Correlation

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Proposition 5.10: the constants are absolute and precede all field and test data. -/
theorem proposition_5_10 :
  ∃ c M : ℝ, 0 < c ∧ 0 < M ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (K : Type) [Field K] [Algebra (ZMod 2) K]
      (e : Module.Basis (Fin n) (ZMod 2) K)
      (τ : Restriction (Fin n)), (fixedCount τ : ℝ) ≤ (n : ℝ)/4 →
    ∀ (k b : ℕ), 1 ≤ b → b ≤ k → ∀ (q : ℝ), 0 < q → q ≤ 1 →
    ∀ (L : ℕ), 1 ≤ L →
    let p := (b : ℝ)/(64*k)
    let m := q*p*Fintype.card (Live τ)
    M ≤ m → Real.logb 2 (8*L) ≤ m/16 → m*L ≤ (n : ℝ)/64 →
    (∀ t : ℕ, (t : ℝ) ≤ 2*m →
      HasClosureDecomp b (Fin t) ((2 : ℝ)^((t : ℝ)/32)) L) →
    restrExpect q (fun φ => corr k (restrict φ (restrict τ (sgn (inverseTrace e))))) ≤
      (2 : ℝ)^(-c*m) := by sorry

end ParityBarrier563.Trilinear.Supplement
