-- Prove2me | Theorems.Thm_QAlgorithms_Papers_LeverrierZemor23Decode_sequentialDecoder_valid
-- name    : QAlgorithms.Papers.LeverrierZemor23Decode.sequentialDecoder_valid
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:04:36.058444+00:00
-- url     : https://prove2.me/theorems/bd502ffd-65ab-4db5-9550-c1b66abdaadf
-- title:
--   Sequential decoder of quantum Tanner codes corrects linear-weight errors in linearly many iterations
-- statement:
--   This is the correctness and iteration bound of the sequential decoder for quantum Tanner codes (Leverrier–Zémor, Theorem 13 with the bound established in its proof).
--
--   Fix $\varepsilon\in(0,1)$ and constants $\delta,\kappa>0$. There is $\Delta_0$ (depending only on $\varepsilon,\delta,\kappa$) such that the following holds for every $\Delta\ge\Delta_0$. Let $G$ be a finite group with self-inverse subsets $A=A^{-1}$, $B=B^{-1}$ of size $|A|=|B|=\Delta$ such that the left Cayley graph $\mathrm{Cay}(G,A)$ and the right Cayley graph $\mathrm{Cay}(G,B)$ are connected, non-bipartite ($-\Delta$ is not an adjacency eigenvalue) and Ramanujan (every adjacency eigenvalue $\lambda\ne\pm\Delta$ has $|\lambda|\le2\sqrt{\Delta-1}$). Let $C_A\subseteq\mathbb F_2^A$, $C_B\subseteq\mathbb F_2^B$ be linear codes with $\dim C_A+\dim C_B=\Delta$, such that $C_A$, $C_B$, $C_A^\perp$, $C_B^\perp$ all have minimum distance at least $\delta\Delta$, and both dual tensor codes $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$ and $C_A^\perp\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B^\perp$ are $\kappa$-product-expanding (every codeword $x$ is $c+r$ with $|x|\ge\kappa\Delta(\|c\|+\|r\|)$, counting nonzero columns of $c$ and nonzero rows of $r$). Let $Q\cong G\times A\times B$ be the set of squares of the quadripartite left-right Cayley complex, $n=|Q|$, and let $\mathcal Q=(C_0,C_1)$ be the quantum Tanner code.
--
--   Let $e\in\mathbb F_2^Q$ be a $\sigma_x$-type error with
--
--   $$
--   |e|<\frac{1}{2^{11}}\min\Big(\frac{\varepsilon^3}{16},\kappa\Big)(1-\varepsilon)\,\delta^2\kappa^2\,\frac{n}{\Delta}.
--   $$
--
--   For each $v\in V_1=V_{01}\cup V_{10}$ let $\varepsilon_v$ be any minimum-weight local vector on $Q(v)$ with the same local syndrome as $e_v$, and let $Z=\sum_{v\in V_1}\varepsilon_v$ be the mismatch. Consider any run of the sequential mismatch decomposition (Algorithm 2 with parameter $\varepsilon$, with any of its choices of vertex $v\in V_{ij}$ and nonzero local dual tensor codeword $x_v=c_v+r_v$ with $|\hat Z|-|\hat Z+x_v|\ge(1-\varepsilon)|x_v|$ and $\|c_v\|+\|r_v\|$ minimal, updating $\hat C_j\mathrel{+}=c_v$, $\hat R_i\mathrel{+}=r_v$, $\hat Z\mathrel{+}=x_v$), started from $\hat C=\hat R=0$, $\hat Z=Z$, after $m$ iterations. Then:
--
--   1. $(1-\varepsilon)\,m\le4|e|$, i.e. the decoder makes at most $4|e|/(1-\varepsilon)$ iterations, a number linear in $n$;
--   2. if $\hat Z\neq0$, a further iteration is possible (the decoder never returns Failure);
--   3. if $\hat Z=0$, the output $\hat e=\sum_{v\in V_{10}}\varepsilon_v+\hat C_0+\hat R_1$ satisfies $e+\hat e\in C_0^\perp$, the span of the $\sigma_x$-generators (codewords of $C_A\otimes C_B$ on the $Q$-neighbourhoods of $V_0$): $\hat e$ is equivalent to $e$ up to the stabilizer group.
--
--   This is the paper's linear-time decoding guarantee: quantum Tanner codes built from Ramanujan left-right Cayley complexes and robust local codes admit a sequential decoder correcting every error of weight linear in the code length.
--
--   **Formalization Note** The squares are indexed injectively by $G\times A\times B$; vertices are $G\times\{0,1\}^2$ with the paper's labelling $\varphi_v$ (p.10). Algorithm 2 is a nondeterministic step relation, so the statement quantifies over all runs and over all choices of the $\varepsilon_v$. Only the $\sigma_x$ case is stated, as in the paper's proof (the $\sigma_z$ case is symmetric). The group $G$ ranges over `Type` (universe 0).
-- source:
--   Decoding quantum Tanner codes (Leverrier, Zemor), arXiv:2208.05537v3, Theorem 13, PDF p. 20. https://arxiv.org/abs/2208.05537v3 . PDF SHA-256: 00e49f39b53afc7f461236c1dba37dcfe884671b342374d816226270881e2779.

import Definitions.Def_QAlgorithms_Defs_TannerDecoder
set_option autoImplicit false

namespace QAlgorithms.Papers.LeverrierZemor23Decode

open QAlgorithms

/-- LZ-dec Theorem 13 (p.20), with the iteration bound of its proof (p.24–25: Lemma 17,
`|Z| ≤ 4|e|`, and `(1 − ε)(|x₁| + ⋯ + |x_m|) ≤ |Z|`).

Fix `ε ∈ (0, 1)` and the constants `δ, κ > 0`. For every large enough constant `Δ` (standing
assumption p.4, p.11: "For a constant `∆` large enough"; `Δ₀` depends on `ε, δ, κ` only), for every
finite group `G` with self-inverse generating sets `A, B`, `|A| = |B| = Δ`, whose left Cayley graph
`Cay(G, A)` and right Cayley graph `Cay(G, B)` are non-bipartite Ramanujan (p.7, p.10), and local
codes `C_A ⊆ F₂^A`, `C_B ⊆ F₂^B` with `dim C_A + dim C_B = Δ` (p.11), all four of `C_A, C_B, C_A^⊥,
C_B^⊥` of distance `≥ δΔ` (p.4), and both dual tensor codes `C_A ⊗ F₂^B + F₂^A ⊗ C_B`,
`C_A^⊥ ⊗ F₂^B + F₂^A ⊗ C_B^⊥` `κ`-product-expanding (p.12): for every σx-type error
`e ∈ F₂^Q` with `|e| < 2^{-11} min(ε³/16, κ)(1 − ε) δ² κ² n / Δ` (`n = |Q| = |G| Δ²`), for every
choice of minimum-weight local corrections `ε_v` (`v ∈ V₁`, Algorithm 1 lines 2–4), and for every
run of the sequential decoder (Algorithm 2, all nondeterministic choices) from the mismatch
`Z = Σ_{v ∈ V₁} ε_v`:
1. the run has made at most `4|e| / (1 − ε)` iterations (linear in `n`);
2. if the current mismatch is nonzero, an iteration is available (the decoder never fails);
3. if the current mismatch is zero, the output `ê = Σ_{v ∈ V₁₀} ε_v + Ĉ₀ + R̂₁` satisfies
   `e + ê ∈ C₀^⊥` (the span of the σx-generators: a valid correction). -/
theorem sequentialDecoder_valid :
    ∀ ε δ κ : ℝ, 0 < ε → ε < 1 → 0 < δ → 0 < κ →
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
    ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (A B : Finset G),
      A.card = Δ → B.card = Δ →
      (∀ a ∈ A, a⁻¹ ∈ A) → (∀ b ∈ B, b⁻¹ ∈ B) →
      IsRamanujanAdj (leftCayleyAdj A) Δ →
      (∀ k, ascEigenvalues (leftCayleyAdj A) k ≠ -(Δ : ℝ)) →
      IsRamanujanAdj (rightCayleyAdj B) Δ →
      (∀ k, ascEigenvalues (rightCayleyAdj B) k ≠ -(Δ : ℝ)) →
      ∀ (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2)),
      Module.finrank (ZMod 2) CA + Module.finrank (ZMod 2) CB = Δ →
      HasMinDistAtLeast CA (δ * Δ) → HasMinDistAtLeast CB (δ * Δ) →
      HasMinDistAtLeast (codeDual CA) (δ * Δ) → HasMinDistAtLeast (codeDual CB) (δ * Δ) →
      IsProductExpanding CA CB Δ κ → IsProductExpanding (codeDual CA) (codeDual CB) Δ κ →
      ∀ e : G × A × B → ZMod 2,
      (hammingNorm e : ℝ) < 1 / 2 ^ 11 * min (ε ^ 3 / 16) κ * (1 - ε) * δ ^ 2 * κ ^ 2 *
          (Fintype.card (G × A × B) : ℝ) / Δ →
      ∀ εsel : G × (Bool × Bool) → A × B → ZMod 2,
      (∀ v : G × (Bool × Bool), v.2.1 ≠ v.2.2 → IsMinLocalCorrection CA CB e v (εsel v)) →
      ∀ (s : ℕ → SeqDecState (G × A × B)) (m : ℕ),
        IsSeqDecRun CA CB ε (qtMismatch εsel) s m →
        (1 - ε) * (m : ℝ) ≤ 4 * (hammingNorm e : ℝ) ∧
        ((s m).Z ≠ 0 → ∃ s', SeqDecStep CA CB ε (s m) s') ∧
        ((s m).Z = 0 → e + seqDecOutput εsel (s m) ∈ qtSigmaXSpan CA CB) := by sorry

end QAlgorithms.Papers.LeverrierZemor23Decode
