-- Prove2me | Theorems.Thm_QCollLB_lemma_3_1
-- name    : QCollLB.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:25.6902+00:00
-- url     : https://prove2.me/theorems/422d3945-3359-4555-bf36-abc7055a1f14
-- title:
--   Lemma 3.1 — one-round orthogonality
-- statement:
--   Let $\mathcal A$ be a one-round algorithm with $t$ parallel queries to the shared phase oracle on $x\in\mathbb Z_q^n$. Then there are vectors $u_a$ in the algorithm register $A$ (indexed by a finite set) and charge labels $\sigma_a:[n]\to\mathbb Z_q$ such that
--
--   1. $\langle u_a,u_b\rangle=0$ for $a\ne b$ and $\sum_a\|u_a\|^2=1$;
--   2. the charged set $S_a=\{i:\sigma_a(i)\ne0\}$ has $|S_a|\le t$;
--   3. for every input $x$, with $h_a(x)=\prod_{i\in S_a}\omega_q^{\sigma_a(i)x_i}$,
--   $$
--   \psi_{x,1}=(O_x^{\otimes t}\otimes I_W)U_0|0\rangle_A=\sum_a h_a(x)\,u_a,\qquad \psi'_{x,1}=\sum_a h_a(x)\,U_1u_a .
--   $$
--
--   The vectors $u_a$ depend only on the algorithm. This is the structural fact that makes one-round algorithms tractable: the input enters only through phases attached to orthogonal algorithm vectors.
--
--   Differences from the source:
--   - encoding: the purified joint state φ_1 = Σ_a |ν,h_a⟩ ⊗ u_a for every input distribution ν → the same decomposition of ψ_{x,1} for every single input x, with u_a independent of x; reason: φ_1 = Σ_x √ν(x)|x⟩ ⊗ ψ_{x,1}; the two forms are equivalent (point masses for one direction, summation for the other)
--   - encoding: index a over basis query records → an arbitrary finite index type; reason: the conclusion is existential in the index set; the basis records are one choice
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Lemma 3.1, p.18

import Mathlib
import Definitions.Def_QCollLB_OneRound

namespace QCollLB

open QAlgorithms

/-- **Lemma 3.1 (One-round orthogonality)** (Peng–Wu, *Quantum Lower Bounds for Collision
Problems*, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Lemma 3.1, p.18). For every one-round
`t`-query algorithm there are vectors `u_a` of the algorithm register, pairwise orthogonal with
`Σ_a ‖u_a‖² = 1`, and charge labels `σ_a : [n] → Z_q` with at most `t` charged positions
`S_a = Supp σ_a`, such that for every input `x` the post-query state is
`ψ_{x,1} = Σ_a h_a(x) u_a` with `h_a(x) = ∏_{i ∈ S_a} ω_q^{σ_a(i) x_i}`, and the final state is
`ψ'_{x,1} = Σ_a h_a(x) U_1 u_a`.

**Formalization Note.** The paper states the purified form `φ_1 = Σ_a |ν, h_a⟩_X ⊗ u_a` for every
input distribution `ν`, with `u_a` independent of `ν`; since `φ_1 = Σ_x √ν(x) |x⟩ ⊗ ψ_{x,1}`, this is
equivalent to the per-input form stated here (take `ν` a point mass for one direction, sum for the
other). The index set of the `u_a` is an arbitrary finite type `α`. `ψ_{x,1}` is
`(O_x^{⊗t} ⊗ I_W) U_0 |0⟩_A`, i.e. the oracle applied to `A.stateAt _ 0`. -/
theorem lemma_3_1 {n q t b : ℕ} [NeZero q] (A : OneRoundAlg n q t b) :
    ∃ (α : Type) (_ : Fintype α)
      (u : α → EuclideanSpace ℂ (((Fin t → Fin n) × (Fin t → ZMod q)) × Fin b))
      (σ : α → Fin n → ZMod q),
      (∀ a a', a ≠ a' → inner ℂ (u a) (u a') = 0) ∧
      ∑ a, ‖u a‖ ^ 2 = 1 ∧
      (∀ a, (Finset.univ.filter fun i => σ a i ≠ 0).card ≤ t) ∧
      ∀ x : Fin n → ZMod q,
        act (Matrix.kronecker (parPhaseOracle x) (1 : Matrix (Fin b) (Fin b) ℂ))
            (A.stateAt (parPhaseOracle x) 0) =
          ∑ a, (∏ i ∈ Finset.univ.filter (fun i => σ a i ≠ 0),
            SelectiveDPT.rootPow q (σ a i * x i)) • u a ∧
        A.finalState (parPhaseOracle x) =
          ∑ a, (∏ i ∈ Finset.univ.filter (fun i => σ a i ≠ 0),
            SelectiveDPT.rootPow q (σ a i * x i)) • act (A.U 1 : Matrix _ _ ℂ) (u a) := by sorry

end QCollLB
