-- Prove2me | Theorems.Thm_QTDecode_Parallel_theorem_20
-- name    : QTDecode.Parallel.theorem_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:57.894598+00:00
-- url     : https://prove2.me/theorems/ee77e8a0-b105-4ff0-a50f-6f5c87f7615c
-- title:
--   Theorem 20, p. 30 (= Theorem 3, p. 6; κ term corrected to κ/4) — the parallel decoder corrects every σx-error of weight < 2⁻¹² min(ε³/16, κ/4) δ²κ² n/Δ in logarithmically many rounds
-- statement:
--   Fix $\varepsilon\in(0,1/6)$ and $\delta,\kappa>0$. There is $\Delta_0$ such that the following holds for every $\Delta\ge\Delta_0$. Let $G$ be a finite group with $A=A^{-1}$, $B=B^{-1}\subseteq G$, $|A|=|B|=\Delta$, such that $\mathrm{Cay}(G,A)$ and $\mathrm{Cay}(G,B)$ are non-bipartite Ramanujan graphs, and consider the quantum Tanner code on the quadripartite left-right Cayley complex, of length $n=|Q|=|G|\Delta^2$, with local codes $C_A\subseteq\mathbb F_2^A$, $C_B\subseteq\mathbb F_2^B$ such that $\dim C_A+\dim C_B=\Delta$, the four codes $C_A,C_B,C_A^\perp,C_B^\perp$ have minimum distance at least $\delta\Delta$, and both dual tensor codes $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$ and $C_A^\perp\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B^\perp$ are $\kappa$-product-expanding. Let $e$ be a $\sigma_x$-type error with
--   $$|e|\ <\ \frac1{2^{12}}\min\Big(\frac{\varepsilon^3}{16},\frac\kappa4\Big)\,\delta^2\kappa^2\,\frac n\Delta,$$
--   let $\varepsilon_v$ ($v\in V_1$) be any minimum-weight local corrections, $Z=\sum_{v\in V_1}\varepsilon_v$ the mismatch, and consider any run of the parallel mismatch decomposition (Algorithm 3) from $Z$, with $\hat Z_k$ the mismatch after $k$ rounds and $\theta=\frac14\big(\frac14-\frac32\varepsilon\big)$. Then:
--
--   1. every round contracts the mismatch: $|\hat Z_{k+1}|\le(1-\theta)\,|\hat Z_k|$ for all $k$;
--   2. in particular $\hat Z_k=0$ as soon as $(1-\theta)^k\cdot 4|e|<1$, so the decoder finishes after $O(\log|e|)$ rounds;
--   3. whenever $\hat Z_k=0$, the output $\hat e=\sum_{v\in V_{10}}\varepsilon_v+\hat C_0+\hat R_1$ is a valid correction: $e+\hat e$ lies in the span of the $\sigma_x$-type generators, i.e. $e$ and $\hat e$ differ by an element of the stabilizer group.
--
--   This is the main result of the paper: a decoder for asymptotically good quantum LDPC codes that corrects adversarial errors of weight linear in the code length using a logarithmic number of rounds of local, parallel updates.
--
--   **Formalization Note** The page prints $\min(\varepsilon^3/16,\kappa)$. The correctness step of the proof (p. 31) compares $|e+\hat e|\le\frac{10}\kappa|e|$ with the minimum distance $\delta^2\kappa^2n/(256\Delta)$ of Theorem 9, whose own proof only supports $\delta^2\kappa^2n/(1024\Delta)$; with the corrected distance the argument goes through for $\min(\varepsilon^3/16,\kappa/4)$, which is what is stated here (a weaker claim than the printed one). "$\Delta$ large enough" (needed by Theorem 12 and Lemma 8) is $\exists\Delta_0$ depending on $\varepsilon,\delta,\kappa$. Theorem 3 (p. 6) reads "Fix $\varepsilon\in(0,1/2)$, and $\mu\in(\varepsilon,1/6)$"; $\mu$ appears nowhere else and Lemma 18 needs $\varepsilon<1/6$, so Theorem 20's range is used. "Logarithmic time" is the number of rounds, made explicit by clauses 1–2 with the paper's constants ($\theta$ from Lemma 18, $|Z|\le4|e|$ from Lemma 17); each round is four parallel substeps of local work. Only $\sigma_x$-type errors are treated, as in the paper; the $\sigma_z$ case is the same statement for $(C_A^\perp,C_B^\perp)$ with $V_0$ and $V_1$ exchanged. Runs are all sequences of rounds in which every vertex flips an admissible local codeword of maximum weight (or nothing if none is admissible).
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 30, Theorem 20 (= p. 6, Theorem 3); proof pp. 30–31

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Theorem 20, p. 30 (= Theorem 3, p. 6), with the `κ` term corrected to `κ/4` and "`Δ` large
enough" made explicit. Fix `ε ∈ (0, 1/6)`, `δ, κ > 0`. There is `Δ₀` such that for `Δ ≥ Δ₀`, every
quadripartite left-right Cayley complex with non-bipartite Ramanujan `Cay(G, A)`, `Cay(G, B)`
(`|A| = |B| = Δ`, `A = A⁻¹`, `B = B⁻¹`), local codes with `dim C_A + dim C_B = Δ`, `C_A, C_B, C_A^⊥,
C_B^⊥` of minimum distance at least `δΔ`, both dual tensor codes `κ`-product-expanding; every
`σ_x`-type error `e` with `|e| < 2⁻¹² min(ε³/16, κ/4) δ²κ² n/Δ`; every choice of minimum-weight local
corrections `ε_v` (`v ∈ V₁`); and every run of the parallel decoder from the mismatch
`Z = Σ_{v ∈ V₁} ε_v`:
1. every round multiplies the mismatch weight by at most `1 − (1/4)(1/4 − 3ε/2)`;
2. hence the mismatch is zero after `k` rounds as soon as `(1 − (1/4)(1/4 − 3ε/2))^k · 4|e| < 1`
   (logarithmically many rounds);
3. once the mismatch is zero, the output `ê = Σ_{v ∈ V₁₀} ε_v + Ĉ₀ + R̂₁` is a valid correction:
   `e + ê` lies in the span of the `σ_x`-generators. -/
theorem theorem_20 :
    ∀ ε δ κ : ℝ, 0 < ε → ε < 1 / 6 → 0 < δ → 0 < κ →
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
      (hammingNorm e : ℝ) < 1 / 2 ^ 12 * min (ε ^ 3 / 16) (κ / 4) * δ ^ 2 * κ ^ 2 *
          (Fintype.card (G × A × B) : ℝ) / Δ →
      ∀ εsel : G × (Bool × Bool) → A × B → ZMod 2,
      (∀ v : G × (Bool × Bool), v.2.1 ≠ v.2.2 → IsMinLocalCorrection CA CB e v (εsel v)) →
      ∀ s : ℕ → SeqDecState (G × A × B), IsParDecRun CA CB (qtMismatch εsel) s →
        (∀ k : ℕ, (hammingNorm (s (k + 1)).Z : ℝ) ≤
          (1 - 1 / 4 * (1 / 4 - 3 / 2 * ε)) * (hammingNorm (s k).Z : ℝ)) ∧
        (∀ k : ℕ, (1 - 1 / 4 * (1 / 4 - 3 / 2 * ε)) ^ k * (4 * (hammingNorm e : ℝ)) < 1 →
          (s k).Z = 0) ∧
        (∀ k : ℕ, (s k).Z = 0 → e + seqDecOutput εsel (s k) ∈ qtSigmaXSpan CA CB) := by sorry

end QTDecode.Parallel
