-- Prove2me | Theorems.Thm_ProxGapTight_lemma_3_5_syndromes
-- name    : ProxGapTight.lemma_3_5_syndromes
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T07:52:47.990904+00:00
-- url     : https://prove2.me/theorems/b31fe786-3963-4072-a30a-005d2239c5e6
-- title:
--   Lemma 3.5 — pairwise independent incidence syndromes $\Psi_0(u_W)$
-- statement:
--   Let $p$ be a prime, $Q=p^a$, $m\ge4$, and $q=Q^{2m}$. Let $X$ be the set of lines of $\mathbb F_Q^m$ and $u_W\in\mathbb F_q^X$ the incidence vector of $W\in\mathrm{Gr}(m-2,\mathbb F_Q^m)$. There is an $\mathbb F_q$-linear map $\Psi_0:\mathbb F_q^X\to\mathbb F_q^2$ such that:
--
--   1. **Nonzero incidence syndromes.** $\Psi_0(u_W)\neq0$ for every $W$.
--   2. **Independent syndrome directions.** For distinct $W,W'$, the vectors $\Psi_0(u_W)$ and $\Psi_0(u_{W'})$ are linearly independent over $\mathbb F_q$.
--
--   The base code $C_m$ of Lemma 3.2 is the kernel of $\Psi_0$ on $\mathrm{span}_{\mathbb F_q}(U_m)$: two incidence vectors can never combine into a codeword, while three always can.
--
--   **Formalization Note** $\mathbb F_Q$ and $\mathbb F_q$ are any fields of orders $p^a$ and $(p^a)^{2m}$. The paper identifies $\mathbb F_Q^m$ with $V=\mathbb F_{Q^m}$, so $\mathrm{Gr}(m-2,V)$ is the set of codimension-two subspaces of $\mathbb F_Q^m$.
--
--   Differences from the source:
--   - generalization: Q = p^a > 32, Q ∉ {49, 121} and m sufficiently large (context of Lemma 3.2) → every prime p, every a, every m ≥ 4; reason: the proof (p.10) uses only m ≥ 4 ('clearly true for m = 4. For m ≥ 5 …'); the statement specializes to the paper's p, Q, m
--   - generalization: F_Q and F_q = F_{Q^{2m}} → any fields with Fintype.card = p ^ a and (p ^ a) ^ (2 * m); reason: all fields of these orders are isomorphic to them; the statement specializes to them
--   - encoding: Ψ₀ : span_{F_q}(U_m) → F_q^2 → Ψ₀ : (Lines K m → F) →ₗ[F] (Fin 2 → F); reason: the restriction of such a map to span_{F_q}(U_m) is the printed map with the same values on every u_W, and every linear map on the subspace extends to the whole space
--   - encoding: Gr(m − 2, V) with V = F_{Q^m} identified with F_Q^m → Codim2 K m, codimension-two subspaces of K^m; reason: the identification of p.9
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), Lemma 3.5, pp.9–10 (proof p.10)

import Mathlib
import Definitions.Def_ProxGapTight_incVec

namespace ProxGapTight

/-- **Lemma 3.5**, Kominers, Thaler, Zheng, manuscript (Sept. 2026), pp.9–10 (proof p.10). Let
`q := q_m = Q^{2m}`. There is an `F_q`-linear map `Ψ₀ : span_{F_q}(U_m) → F_q^2` with
1. `Ψ₀(u_W) ≠ 0` for every `W ∈ Gr(m − 2, V)`;
2. `Ψ₀(u_W)` and `Ψ₀(u_{W'})` linearly independent over `F_q` for distinct `W, W'`.

**Formalization Note.** `F_Q` is any field `K` of order `Q = p^a` and `F_q` any field `F` of order
`Q^{2m}`; `V = F_{Q^m}` is identified with `K^m` (p.9), so `Gr(m − 2, V)` is `Codim2 K m` and the
incidence vectors, viewed in `F^X`, are `incVec F W`. `Ψ₀` is a linear map on all of `F^X`, whose
restriction to `span_{F_q}(U_m)` is the printed map (and any map on the subspace extends). The
statement is for every `m ≥ 4`, the only condition the proof (p.10) uses; the conditions
`Q > 32`, `Q ∉ {49, 121}` of the surrounding Lemma 3.2 are not needed. -/
theorem lemma_3_5_syndromes (p a m : ℕ) [Fact p.Prime] (hm : 4 ≤ m)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = p ^ a)
    (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = (p ^ a) ^ (2 * m)) :
    ∃ Ψ₀ : (Lines K m → F) →ₗ[F] (Fin 2 → F),
      (∀ W : Codim2 K m, Ψ₀ (incVec F W) ≠ 0) ∧
      (∀ W W' : Codim2 K m, W ≠ W' →
        LinearIndependent F ![Ψ₀ (incVec F W), Ψ₀ (incVec F W')]) := by sorry

end ProxGapTight
