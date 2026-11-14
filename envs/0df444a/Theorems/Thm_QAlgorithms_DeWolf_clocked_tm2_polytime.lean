-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_clocked_tm2_polytime
-- name    : QAlgorithms.DeWolf.clocked_tm2_polytime
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:25:44.03527+00:00
-- url     : https://prove2.me/theorems/1197a675-9737-4c54-929e-e26b72cf49fb
-- title:
--   A multi-stack machine that halts in polynomial time on a set of valid inputs can be clocked into a polynomial-time computable function
-- statement:
--   Let $M$ be a finite multi-stack (TM2) machine whose input and output stack alphabets are identified with $\{0,1\}$, and let $c,d$ be constants. Suppose that on every input $a$ from an indexed family $(\mathit{inp}_i)$ the machine halts within $(|a|+c)^d$ steps with $\mathit{out}_i$ on its output stack. Then there is a function $u:\{0,1\}^*\to\{0,1\}^*$ that is polynomial-time computable (by a machine that halts on every input) with $u(\mathit{inp}_i)=\mathit{out}_i$ for all $i$. In symbols: $$\big(\forall i,\ M(\mathit{inp}_i)\downarrow_{\le (|\mathit{inp}_i|+c)^d} \mathit{out}_i\big) \implies \exists u \in \mathrm{FP},\ \forall i,\ u(\mathit{inp}_i)=\mathit{out}_i.$$
-- source:
--   S. Arora and B. Barak, Computational Complexity: A Modern Approach (Cambridge, 2009), Section 1.2 (time-constructible functions: a machine is run against a step counter and stopped after T(n) steps); used implicitly in R. de Wolf, Quantum Computing: Lecture Notes, arXiv:1907.09415, Section 20.3, p.187 (polynomial-time classical simulation)

import Mathlib

namespace QAlgorithms.DeWolf

theorem clocked_tm2_polytime {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} (k0 k1 : K)
    [Inhabited (Γ k0)] {Λ σ : Type} [Fintype Λ] [Fintype σ] [Fintype (Γ k0)]
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) (main : Λ) (c d : ℕ) (s0 : σ) (e0 : Γ k0 ≃ Bool) (e1 : Γ k1 ≃ Bool)
    {I : Type} (inp out : I → List Bool)
    (h : ∀ i, ∃ t ≤ ((inp i).length + c) ^ d, ∃ cf : Turing.TM2.Cfg Γ Λ σ,
      (flip bind (Turing.TM2.step M))^[t + 1]
        (some ⟨some main, s0, Function.update (fun k => ([] : List (Γ k))) k0 ((inp i).map e0.symm)⟩) =
        some cf ∧ cf.l = none ∧ cf.stk k1 = (out i).map e1.symm) :
    ∃ u : List Bool → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) u) ∧
      ∀ i, u (inp i) = out i := by sorry

end QAlgorithms.DeWolf
