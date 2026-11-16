-- Prove2me | Theorems.Thm_SATotalCoeffLB_Supplement_theorem_9
-- name    : SATotalCoeffLB.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:32:27.623902+00:00
-- url     : https://prove2.me/theorems/01b2b8d5-5a7a-47a6-8985-e5206c9e0919
-- title:
--   Theorem 9 — without extension variables, averaging extended Sherali–Adams collapses to Sherali–Adams
-- statement:
--   Let $W$ be a finite set of variables, let $P \subseteq \mathbb R[W]/\langle y^2 - 1 : y \in W\rangle$ be a finite set of polynomials, and let $k, M \ge 0$. The following are equivalent.
--
--   1. There is an **averaging extended Sherali–Adams refutation of $P$ without extension variables**: a finite set $Q$ of random variables, a finite family $H$ of polynomials, multipliers $C_p(W, Q)$ for $p \in P$, and $K \in \mathrm{Ker}_{\mathrm{avg}}$ such that
--   $$
--   -1 = \sum_{h \in H} h(W, Q)^2 + \sum_{p \in P} C_p(W, Q)\, p(W) + K(W, Q)
--   $$
--   in $\mathbb R[W, Q]/\langle y^2 - 1 : y \in W \cup Q\rangle$, in which each $h \in H$ depends on at most $k$ variables from $W$ (with unrestricted dependence on $Q$), and
--   $$
--   \mathop{\mathbb E}_{q \leftarrow \{\pm1\}^Q}\Bigl[\sum_{p \in P} \|C_p(W, q)\|_1\Bigr] \le M .
--   $$
--   2. There is a **Sherali–Adams refutation of $P$**: a finite family $H'$ and multipliers $C'_p(W)$ with
--   $$
--   -1 = \sum_{h \in H'} h(W)^2 + \sum_{p \in P} C'_p(W)\, p(W)
--   $$
--   in $\mathbb R[W]/\langle y^2 - 1 : y \in W\rangle$, in which each $h \in H'$ depends on at most $k$ variables, and $\sum_{p \in P} \|C'_p\|_1 \le M$.
--
--   Here $\|f\|_1$ is the sum of the absolute values of the coefficients of the multilinear polynomial $f$, and $\mathrm{Ker}_{\mathrm{avg}}$ is the span of the products $a\, q_j$ with $q_j \in Q$ not appearing in $a$.
--
--   The theorem says that the averaging over random variables, without extension variables, adds no power to Sherali–Adams measured by total coefficient size: neither the locality nor the size bound changes. In particular the lower bound of Theorem 3 also holds for averaging extended Sherali–Adams refutations without extension variables.
--
--   **Formalization Note** Elements of the Boolean quotient rings are real functions on the cube (`CubeFn`), so the identities are equalities of functions. The random-variable set $Q$ is `Fin r` for some $r$, the families $H$ and $H'$ are indexed by `Fin m`, and the multipliers are functions of $p$.
--
--   Differences from the source:
--   - encoding: a finite set $Q$ of random variables → `Fin r` for some $r \in \mathbb N$; reason: every finite set is in bijection with some `Fin r`, and both items are invariant under renaming the variables of $Q$.
--   - encoding: finite families $H$, $H'$ → families indexed by `Fin m` (repetitions allowed); reason: a repeated $h$ is merged as $(\sqrt2\, h)^2$, which depends on the same variables, so the same refutations exist.
--   - encoding: identities in the Boolean quotient rings → equality of functions on $\{\pm1\}^{W}$, $\{\pm1\}^{W\cup Q}$ (published `CubeFn`); reason: for finite variable sets evaluation on the cube is a ring isomorphism.
--   - encoding: $k \ge 0$ → $k \in \mathbb N$; reason: "depends on at most $k$ variables" for real $k$ is the same as for $\lfloor k \rfloor$.
--   - encoding: the variables $W$ of $P$ → a finite type `W`; reason: $P$ consists of polynomials in finitely many variables, as the coefficient norm requires.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Theorem 9, Appendix D, pp.73–74 (the refutation form (1), Ker_avg and the averaging total coefficient size, pp.6–7)

import Mathlib
import Definitions.Def_SATotalCoeffLB_DependsOnAtMost
import Definitions.Def_SATotalCoeffLB_Supplement_kerAvg
import Definitions.Def_SATotalCoeffLB_Supplement_liftW
import Definitions.Def_SATotalCoeffLB_Supplement_avgTotalCoeffSize
import Definitions.Def_SATotalCoeffLB_Supplement_DependsOnAtMostFromW

namespace SATotalCoeffLB.Supplement

open SATotalCoeffLB

/-- **Theorem 9 (No-extension collapse)**, Appendix D, pp.73–74, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).
Let `P ⊆ ℝ[W]/⟨y² − 1 : y ∈ W⟩` be a finite set of polynomials and `k, M ≥ 0`. The following
are equivalent:
1. an averaging extended Sherali–Adams refutation of `P` without extension variables: a finite set
   `Q` of random variables, a finite family `H`, multipliers `C_p(W, Q)` and `K ∈ Ker_avg` with
   `−1 = ∑_{h ∈ H} h(W, Q)² + ∑_{p ∈ P} C_p(W, Q) p(W) + K(W, Q)` in `ℝ[W, Q]/⟨y² − 1⟩`, each
   `h` depending on at most `k` variables from `W`, and `E_q[∑_p ‖C_p(W, q)‖₁] ≤ M`;
2. a Sherali–Adams refutation `−1 = ∑_{h ∈ H'} h(W)² + ∑_{p ∈ P} C'_p(W) p(W)` in
   `ℝ[W]/⟨y² − 1⟩` with each `h ∈ H'` a `k`-junta and `∑_p ‖C'_p‖₁ ≤ M`.

**Formalization Note** The random-variable set `Q` is `Fin r` for some `r` (every finite set is
in bijection with one); the families `H`, `H'` are indexed by `Fin m`; identities in the Boolean
quotient rings are equalities of functions on the cube (`CubeFn`). `k` is a natural number. -/
theorem theorem_9 {W : Type*} [Fintype W] [DecidableEq W] (P : Finset (CubeFn W)) (k : ℕ)
    (M : ℝ) (hM : 0 ≤ M) :
    (∃ (r m : ℕ) (h : Fin m → CubeFn (W ⊕ Fin r)) (C : CubeFn W → CubeFn (W ⊕ Fin r))
        (K : CubeFn (W ⊕ Fin r)),
        K ∈ (kerAvg : Submodule ℝ (CubeFn (W ⊕ Fin r))) ∧
        (∀ i, DependsOnAtMostFromW k (h i)) ∧
        (∀ z, (-1 : ℝ) = ∑ i, h i z ^ 2 + ∑ p ∈ P, C p z * liftW p z + K z) ∧
        avgTotalCoeffSize P C ≤ M) ↔
    (∃ (m : ℕ) (h : Fin m → CubeFn W) (C : CubeFn W → CubeFn W),
        (∀ i, DependsOnAtMost k (h i)) ∧
        (∀ x, (-1 : ℝ) = ∑ i, h i x ^ 2 + ∑ p ∈ P, C p x * p x) ∧
        ∑ p ∈ P, coeffNorm (C p) ≤ M) := by sorry

end SATotalCoeffLB.Supplement
