-- Prove2me | Theorems.Thm_QAlgorithms_Papers_LeverrierZemor22_quantumTanner_weight_reduction
-- name    : QAlgorithms.Papers.LeverrierZemor22.quantumTanner_weight_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:04:52.341671+00:00
-- url     : https://prove2.me/theorems/d3140087-64db-4ea7-aaee-b0fb7e1c97a1
-- title:
--   Quantum Tanner codes: low-weight codewords of C1 are reduced by a local tensor codeword
-- statement:
--   This is the main technical theorem behind quantum Tanner codes.
--
--   **Setting.** Let $G$ be a finite group and $A=A^{-1}$, $B=B^{-1}\subseteq G$ with $|A|=|B|=\Delta$, satisfying the Total No-Conjugacy condition $ag\neq gb$ for all $a\in A$, $b\in B$, $g\in G$. The left-right Cayley complex has vertices $V=V_0\cup V_1$, $V_i=G\times\{i\}$, and squares $Q$, the 4-sets $\{(g,0),(ag,1),(gb,1),(agb,0)\}$. For a vertex $v=(g,i)$ the squares $\{v,(ag,1-i),(gb,1-i),(agb,i)\}$ incident to $v$ are in bijection with $A\times B$, so the restriction $x_v$ of $x\in\mathbb F_2^Q$ to the squares at $v$ is an $A\times B$ array. Let $G_A$, $G_B$ be the bipartite double covers of $\mathrm{Cay}(G,A)$ and $\mathrm{Cay}(G,B)$; we require both to be Ramanujan: connected, and every adjacency eigenvalue other than $\pm\Delta$ has absolute value at most $2\sqrt{\Delta-1}$.
--
--   For codes $C_A\subseteq\mathbb F_2^A$, $C_B\subseteq\mathbb F_2^B$, the tensor code $C_A\otimes C_B$ consists of arrays whose columns lie in $C_A$ and whose rows lie in $C_B$. The dual tensor code is $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$. It is $w$-robust if every codeword $x$ of weight $|x|\le w$ vanishes outside $A'\times B\cup A\times B'$ for some $A'\subseteq A$, $B'\subseteq B$ with $|A'|\le |x|/d_B$ and $|B'|\le |x|/d_A$, where $d_A,d_B$ are the minimum distances. It is $w$-robust with $p$-resistance to puncturing if, for all $A'\subseteq A$, $B'\subseteq B$ with $|A'|=|B'|=\Delta-w'$ and $w'\le p$, the dual tensor code of the punctured codes $C_{A'}$, $C_{B'}$ is $w$-robust. The quantum Tanner code $\mathcal C_1$ is
--   $$\mathcal C_1=\{x\in\mathbb F_2^Q:\ x_v\in C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B\ \text{for every } v\in V_1\}.$$
--
--   **Theorem.** Fix $\varepsilon\in(0,\tfrac12)$, $\gamma\in(\tfrac12+\varepsilon,1)$ and $\delta>0$. There is $\Delta_0$, depending only on $\varepsilon,\gamma,\delta$, such that the following holds for every $\Delta\ge\Delta_0$ and every complex as above. Suppose every nonzero codeword of $C_A$ and of $C_B$ has weight at least $\delta\Delta$, and the dual tensor code is $\Delta^{3/2-\varepsilon/2}$-robust with $\Delta^{\gamma}$-resistance to puncturing. Let $n=|Q|$. Then for every $x\in\mathcal C_1$ with
--   $$0<|x|<\frac{\delta n}{4\Delta^{3/2+\varepsilon}},$$
--   there are a vertex $v\in V_0$ and a tensor codeword $c\in C_A\otimes C_B$ such that the word $y\in\mathbb F_2^Q$ that equals $c$ on the squares at $v$ and is $0$ elsewhere lies in $\mathcal C_1$ and satisfies $|x+y|<|x|$.
--
--   Applied repeatedly, the theorem shows that low-weight codewords of $\mathcal C_1$ lie in $\mathcal C_0^{\perp}$, which gives the linear minimum distance of quantum Tanner codes. It also recovers the local testability of the Dinur et al. code.
--
--   **Formalization Note** The paper says "there exists an infinite family of square complexes". The formal statement instead holds for every left-right Cayley complex that satisfies the hypotheses the proof uses (TNC, Ramanujan double covers). The infinite family is the cited [DEL+21] construction. Minimum distances are taken in $\mathbb N\cup\{\infty\}$, and the bounds $|A'|\le|x|/d_B$ are written as $|A'|\,d_B\le|x|$.
-- source:
--   Quantum Tanner codes (Leverrier, Zemor), arXiv:2202.13641v3, Theorem 1, PDF p. 8. https://arxiv.org/abs/2202.13641v3 . PDF SHA-256: e712a97ef8393e13e631ec38d853dce4520581633583f69f6e72765e51d870a1.

import Definitions.Def_QAlgorithms_Defs_LeftRightComplex
set_option autoImplicit false

namespace QAlgorithms.Papers.LeverrierZemor22

open QAlgorithms

universe u

/-- LZ Theorem 1 (p.8, restated and proved p.19; Definitions 5 and 8, pp.15–16; standing
assumptions of §3.2 and §4.1, pp.11–12, 17).

Fix `ε ∈ (0, 1/2)`, `γ ∈ (1/2 + ε, 1)` and `δ > 0`. There is `Δ₀` (depending only on `ε, γ, δ`)
such that for every `Δ ≥ Δ₀`, every left-right Cayley complex over a finite group `G` with
self-inverse `A, B ⊆ G`, `|A| = |B| = Δ`, satisfying TNC (eq. (1)) and whose double covers
`G_A`, `G_B` are Ramanujan, and all component codes `C_A ⊆ F₂^A`, `C_B ⊆ F₂^B` with minimum distance
`≥ δΔ` whose dual tensor code `C_A ⊗ F₂^B + F₂^A ⊗ C_B` is `w`-robust with `p`-resistance to
puncturing for `w = Δ^{3/2 − ε/2}`, `p = Δ^γ`: every `x ∈ C₁` with `0 < |x| < δn/(4Δ^{3/2+ε})`,
`n = |Q|`, admits a vertex `v ∈ V₀` and a tensor codeword `c ∈ C_A ⊗ C_B` such that the word `y`
supported on `Q(v)` and equal there to `c` lies in `C₁` and `|x + y| < |x|`.

The source's "there exists an infinite family of square complexes `X`" is stated for every
complex satisfying the hypotheses the proof uses (p.19, first sentence); the family itself is
the cited construction of [DEL+21]. -/
theorem quantumTanner_weight_reduction :
    ∀ ε γ δ : ℝ, 0 < ε → ε < 1 / 2 → 1 / 2 + ε < γ → γ < 1 → 0 < δ →
      ∃ Δ0 : ℕ, ∀ Δ : ℕ, Δ0 ≤ Δ →
        ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (A B : Finset G),
          (∀ a ∈ A, a⁻¹ ∈ A) → (∀ b ∈ B, b⁻¹ ∈ B) → A.card = Δ → B.card = Δ →
          IsTNC A B →
          IsRamanujanAdj (bipartiteDoubleCover (leftCayleyAdj A)) Δ →
          IsRamanujanAdj (bipartiteDoubleCover (rightCayleyAdj B)) Δ →
          ∀ (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2)),
            HasMinDistAtLeast CA (δ * Δ) → HasMinDistAtLeast CB (δ * Δ) →
            IsRobustResistant CA CB ((Δ : ℝ) ^ ((3 : ℝ) / 2 - ε / 2)) ((Δ : ℝ) ^ γ) →
            ∀ x ∈ lzTannerCode1 A B CA CB, 0 < hammingNorm x →
              (hammingNorm x : ℝ) <
                δ * ((lzSquares A B).card : ℝ) / (4 * (Δ : ℝ) ^ ((3 : ℝ) / 2 + ε)) →
              ∃ g : G, ∃ c ∈ tensorCode CA CB,
                lzExtend (g, false) c ∈ lzTannerCode1 A B CA CB ∧
                  hammingNorm (x + lzExtend (g, false) c) < hammingNorm x := by
  sorry

end QAlgorithms.Papers.LeverrierZemor22
