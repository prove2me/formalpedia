-- Prove2me | Theorems.Thm_PRUMicrocrypt_lemma_6_6
-- name    : PRUMicrocrypt.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:49.874213+00:00
-- url     : https://prove2.me/theorems/3647baab-9c4c-4fb6-a66a-675607d76f8f
-- title:
--   Lemma 6.6 — from row switches to independent row replacements
-- statement:
--   Fix the outside bits and a finite input set $\mathcal Z$. Let $K\ge1$ keys each carry a row, and let each score $r_z$, $z\in\mathcal Z$, be a function of the rows with values in $[0,1]$. For two candidate rows $S^{(0)}_k,S^{(1)}_k$ per key, a switch vector $s\in\{0,1\}^K$ selects the row $S^{(s_k)}_k$ at each key, giving rows $R_s$. Suppose that for every choice of candidate rows and every $z\in\mathcal Z$,
--
--   $$\Pr_s\Big[\frac1K\sum_k|r_z(R_s)-r_z(R_{s\oplus k})|>a\Big]\le q_{\mathrm{bad}}$$
--
--   for a uniform $s$, where $a\ge0$ and $q_{\mathrm{bad}}\ge0$. If the rows of $R$ are independent and uniform, then for every $b>0$,
--
--   $$\Pr_R\Big[\exists z\in\mathcal Z:\ \mathbb E_{k,S}|r_z(R)-r_z(R^{k\leftarrow S})|>a+b\Big]\le\frac{|\mathcal Z|\,q_{\mathrm{bad}}}{b},$$
--
--   where $k$ is a uniform key and $S$ a fresh uniform row. This is the step from switch stability to the independent-replacement stability (6.1) of Lemma 6.1.
--
--   Differences from the source:
--   - generalization: the clipped scores r_z(O_R) of the universal verifier with the outside bits fixed, K = 2^κ keys, rows of 5nN bits, the input set 𝒵_κ → arbitrary [0,1]-valued functions r z of the rows, any K ≥ 1 keys, any finite nonempty row type, any finite input type; reason: the proof uses only 0 ≤ r_z ≤ 1 and independent uniform rows; the paper's case is K = 2^κ, Row = {0,1}^{5nN}, r z R = r_z(O_R)
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma 6.6, pp.36–37 (row switches §6.4, p.35; R^{k←S} §6.1, p.33)

import Mathlib
import Definitions.Def_PRUMicrocrypt_sensitivity

set_option autoImplicit false

namespace PRUMicrocrypt

/-- **Lemma 6.6 (From row switches to independent replacements).** "Fix the outside bits and a finite
input set 𝒵_κ. Suppose that for every choice of two candidate rows per key and every z ∈ 𝒵_κ,
Pr_s[(1/K) ∑_k |r_z(O_s) − r_z(O_{s⊕k})| > a] ≤ q_bad, where s is uniform, a ≥ 0, and q_bad ≥ 0. If
the rows of R are independent and uniform, then for every b > 0,
Pr_R[∃z ∈ 𝒵_κ : E_{k,S}|r_z(O_R) − r_z(O_{R^{k←S}})| > a + b] ≤ |𝒵_κ| q_bad / b. (6.9)"
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma 6.6, pp.36–37 (row switches §6.4, p.35; `R^{k←S}` §6.1, p.33).

**Formalization Note.** With the outside bits fixed, each score `r_z(O_R)` is a function
`r z : (keys → rows) → [0, 1]` of the rows; the statement is made for every such function, for
`K ≥ 1` keys `Fin K`, any finite nonempty row type and any finite input set `Z`. The candidate
rows are `S₀ S₁ : Fin K → Row`; switch vector `s` selects `S_{s_k} k` at key `k` (`R_s`), and
`s ⊕ k` is `flipBit s k`. `E_{k,S}` is the uniform average over a key `k` and a fresh row `S`;
`R^{k←S}` is `Function.update R k S`. -/
theorem lemma_6_6 (K : ℕ) (hK : 1 ≤ K) {Row Z : Type*} [Fintype Row] [DecidableEq Row]
    [Nonempty Row] [Fintype Z]
    (r : Z → (Fin K → Row) → ℝ) (hr : ∀ z R, 0 ≤ r z R ∧ r z R ≤ 1)
    (a qbad : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ qbad)
    (hyp : ∀ (S₀ S₁ : Fin K → Row) (z : Z),
      unifProb (fun s : Fin K → Bool =>
        a < (1 / (K : ℝ)) * ∑ k : Fin K,
          |r z (fun j => if s j then S₁ j else S₀ j) -
            r z (fun j => if flipBit s k j then S₁ j else S₀ j)|) ≤ qbad) :
    ∀ b : ℝ, 0 < b →
      unifProb (fun R : Fin K → Row => ∃ z : Z,
        a + b < unifAvg (fun p : Fin K × Row => |r z R - r z (Function.update R p.1 p.2)|)) ≤
        (Fintype.card Z : ℝ) * qbad / b := by sorry

end PRUMicrocrypt
