-- Prove2me | Theorems.Thm_PrivPCP_lemma_7_2
-- name    : PrivPCP.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:43:58.217215+00:00
-- url     : https://prove2.me/theorems/718b221b-c01a-40fc-b73f-4f802adeddbc
-- title:
--   Lemma 7.2: axis-line soundness of tensor codes
-- statement:
--   Let $r\ge2$ and let the nonzero linear codes $C_i\subseteq\mathbb F_q^{S'_i}$, $i\in[r]$, have relative distance at least $\Delta$. Put $\Omega'=\prod_{i=1}^rS'_i$, $M=|\Omega'|$ and $\mathcal C=\bigotimes_{i=1}^rC_i$. For a word $w\in\mathbb F_q^{\Omega'}$ let $b_i(w)$ be the fraction of $i$-axis lines $\ell$ with $w|_\ell\notin C_i$. With
--   $$\tau_r(\Delta)=\frac{\Delta^{8r}}{10^6r^{16}},$$
--   the rejection probability of the axis-line test satisfies
--   $$\Pr[\mathsf{Test}(w)\text{ rejects}]=\frac1r\sum_{i=1}^rb_i(w)\ \ge\ \tau_r(\Delta)\,\frac{\mathrm{dist}(w,\mathcal C)}{M}.$$
--
--   This robust testability of tensor codes with unequal components and side lengths gives the soundness of every axis-line check of the circuit tester (38).
--
--   **Formalization Note** Relative distance at least $\Delta$ means $\mathrm{wt}(c)\ge\Delta|S'_i|$ for every nonzero $c\in C_i$, with $\Delta\ge0$.
--
--   Differences from the source:
--   - reading: relative distance at least $\Delta$ → $\Delta\ge0$ and $\mathrm{wt}(c)\ge\Delta|S'_i|$ for nonzero $c\in C_i$; reason: a relative distance is a number in $[0,1]$; for $\Delta<0$ the even power $\Delta^{8r}$ would make the printed inequality false
--   - encoding: $\Pr[\mathsf{Test}(w)\text{ rejects}]=\frac1r\sum_ib_i(w)$ → the inequality for the average $\frac1r\sum_ib_i(w)$; reason: the equality is the definition of the test
--   - encoding: fraction of $i$-axis lines → fraction of points whose $i$-axis line is rejected; reason: each line has $|S'_i|$ points; same value
--   - encoding: $\mathbb F_q$ → any finite field; reason: same instances
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Lemma 7.2, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_PrivPCP_tensorCode

namespace PrivPCP

/-- **Lemma 7.2 (Axis-line soundness)** (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC 2027
submission manuscript (sha256 c2cac1e0…), Lemma 7.2, p.41). Let `r ⩾ 2` and let the nonzero linear codes
`C_i ⊆ 𝔽_q^{S′_i}`, `i ∈ [r]`, have relative distance at least `Δ`. Put `Ω′ = ∏_i S′_i`, `M = |Ω′|`,
`𝒞 = ⊗_i C_i`, and for a word `w` let `b_i(w)` be the fraction of `i`-axis lines `ℓ` with `w|_ℓ ∉ C_i`. With
`τ_r(Δ) = Δ^{8r}/(10⁶ r^{16})`, `(1/r) ∑_i b_i(w) ⩾ τ_r(Δ) · dist(w, 𝒞)/M`.

**Formalization Note** The left side is `Pr[Test(w) rejects]` (the paper's equality defines it). "Relative
distance at least `Δ`" is `wt(c) ⩾ Δ |S′_i|` for every nonzero `c ∈ C_i`, with `Δ ⩾ 0` (a relative distance).
`𝔽_q` is any finite field. -/
theorem lemma_7_2 {F : Type} [Field F] [Fintype F] {r : ℕ} (hr : 2 ≤ r) {S : Fin r → Type}
    [∀ i, Fintype (S i)] (C : ∀ i, Submodule F (S i → F)) (hC : ∀ i, C i ≠ ⊥) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hdist : ∀ i, ∀ c ∈ C i, c ≠ 0 → Δ * Fintype.card (S i) ≤ GoodQLTC.supportCard c)
    (w : (∀ i, S i) → F) :
    Δ ^ (8 * r) / (10 ^ 6 * (r : ℝ) ^ 16) * ((distTo w (tensorCode C) : ℝ) / Fintype.card (∀ i, S i)) ≤
      (1 / (r : ℝ)) * ∑ i, lineRejFrac C i w := by sorry

end PrivPCP
