-- Prove2me | Theorems.Thm_QNoiseStab_theorem_3_4
-- name    : QNoiseStab.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:12.209941+00:00
-- url     : https://prove2.me/theorems/70a2fe69-1f27-44eb-81da-8c4f20407abf
-- title:
--   Theorem 3.4 — $\|\Pi_E\Pi_{B_t}\|^2\le(1-p)^{-t}\max_{x\in E}\Pr[N_p^A(x)\in E]$
-- statement:
--   Let $m\ge1$, $A\subseteq[n]$, let $E\subseteq\mathbb Z_m^{\,n}$ be an event and $\Pi_E$ the projection onto the input states in $E$. Let $0\le p<1$ and $0\le t\le n$. Then
--
--   $$
--   \|\Pi_E\Pi_{B_t}\|^2\ \le\ (1-p)^{-t}\max_{x\in E}\Pr\bigl[N_p^A(x)\in E\bigr].
--   $$
--
--   Equivalently: if $\beta\ge0$ satisfies $\Pr[N_p^A(x)\in E]\le\beta$ for every $x\in E$, then $\|\Pi_E\Pi_{B_t}\psi\|^2\le(1-p)^{-t}\beta\,\|\psi\|^2$ for every vector $\psi\in\mathbb C^{\mathbb Z_m^n}$.
--
--   The probability of an event after $t$ queries is thus controlled by how stable the event is under the classical noise $N_p^A$.
--
--   Differences from the source:
--   - reading: the statement does not restate the range of $p$ → $0\le p<1$; reason: it is the range of Lemma 3.3, which the proof applies; $N_p^A$ is a random variable only for $p\in[0,1]$ and $(1-p)^{-t}$ is undefined at $p=1$
--   - encoding: $\|\Pi_E\Pi_{B_t}\|^2$ → $\|\Pi_E\Pi_{B_t}\psi\|^2\le c\,\|\psi\|^2$ for every $\psi$; reason: $\|M\|^2=\sup_{\|\psi\|=1}\|M\psi\|^2$
--   - encoding: $\max_{x\in E}\Pr[N_p^A(x)\in E]$ → any $\beta\ge0$ with $\Pr[N_p^A(x)\in E]\le\beta$ for all $x\in E$; reason: the maximum (with $\max\emptyset=0$) is such a $\beta$ and the bound increases with $\beta$
--   - encoding: $E\subseteq[m]^n$ → `E : Finset (Fin n → ZMod m)`; reason: Lean convention; 0-based coordinates
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Theorem 3.4, p.12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QNoiseStab_projLowDeg
import Definitions.Def_QNoiseStab_projEvent
import Definitions.Def_QNoiseStab_noiseProb

namespace QNoiseStab

/-- **Theorem 3.4** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.12). Let `A ⊆ [n]` and `E ⊆ [m]ⁿ` be some event. If `Π_E` is the projection onto the
input states that correspond to `E`, then for `0 ≤ t ≤ n`,
`‖Π_E Π_{B_t}‖² ≤ (1 − p)^{-t} max_{x∈E} Pr[N_p^A(x) ∈ E]`.

**Formalization Note** `[m]` is `ZMod m`. The range `0 ≤ p < 1` is that of Lemma 3.3, which the
proof applies (`N_p^A` is a random variable for `p ∈ [0, 1]`, and `(1 − p)^{-t}` is undefined at
`p = 1`). The squared operator norm is stated in its equivalent pointwise form
`‖Π_E Π_{B_t} ψ‖² ≤ c ‖ψ‖²` for every vector `ψ`. The maximum is encoded by any `β ≥ 0` bounding
`Pr[N_p^A(x) ∈ E]` for every `x ∈ E` (the maximum itself is such a `β`, and `max ∅ = 0`). -/
theorem theorem_3_4 {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (E : Finset (Fin n → ZMod m))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (t : ℕ) (ht : t ≤ n) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ∀ x ∈ E, noiseProb p A x E ≤ β) (ψ : EuclideanSpace ℂ (Fin n → ZMod m)) :
    ‖QAlgorithms.act (projEvent E * projLowDeg t) ψ‖ ^ 2 ≤
      ((1 - p) ^ t)⁻¹ * β * ‖ψ‖ ^ 2 := by sorry

end QNoiseStab
