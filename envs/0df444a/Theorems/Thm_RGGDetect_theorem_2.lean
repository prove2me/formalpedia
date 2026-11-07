-- Prove2me | Theorems.Thm_RGGDetect_theorem_2
-- name    : RGGDetect.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:04.752197+00:00
-- url     : https://prove2.me/theorems/bca27cdb-c85b-4fae-b34e-5bd61434dec2
-- title:
--   Theorem 2 — $\mathrm{KL}(P_{\mathrm{RGG}}\|P_{\mathrm{ER}})\le n'K\le n'\Delta+o(1)$
-- statement:
--   Assume the setting of Theorem 1 and let $n'=n-1$. With $K=\mathbb E_{G_{n'}}[\mathrm{KL}(\mathcal L(Y\mid G_{n'})\|Q)]$ and $\Delta$ the truncated $\chi^2$-divergence (9),
--
--   $$
--   \mathrm{KL}(P_{\mathrm{RGG}}\|P_{\mathrm{ER}})\le n'K\le n'\Delta+o(1).
--   $$
--
--   Consequently, to prove Theorem 1 it suffices to prove $\Delta=o(1/n)$.
--
--   This reduces the KL divergence of the whole graph, by the chain rule and data processing, to the row likelihood of a single new vertex.
--
--   **Formalization Note** The statement is made for every value of the slack $B^*$ in $r^+$. It has three parts: the first inequality for all large $n$; a sequence $e_n\to0$ (chosen after the sequences) with $n'K\le n'\Delta+e_n$ for all large $n$; and the implication $n\Delta_n\to0\Rightarrow\mathrm{KL}\to0$.
--
--   Differences from the source:
--   - generalization: the standing hypotheses (1) of Theorem 1, for all n → sequences in `Regime δ p d τ`: each hypothesis for all large n; reason: the statement is asymptotic, so sequences satisfying (1) for all n are covered
--   - generalization: B* a suitably large constant → every B* ∈ ℕ; reason: the proof uses only Q((T⁺)ᶜ) ≤ n^{-30}, which holds for every B* ≥ 0; the statement for all B* contains the suitably large ones
--   - encoding: o(1); 'it suffices to prove Δ = o(1/n)' → a sequence e → 0 chosen after the sequences; the implication n·Δ_n → 0 ⇒ KL → 0; reason: the paper's asymptotic notation; Δ ≥ 0, so Δ = o(1/n) is n·Δ_n → 0
--   - encoding: KL and K real, Δ real → KL and K in [0, ∞], compared with ENNReal.ofReal(n′Δ + e_n); reason: Mathlib's KL takes values in [0, ∞]
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Theorem 2, eq. (10), p.4 (PDF p.6)

import Mathlib
import Definitions.Def_RGGDetect_Regime
import Definitions.Def_RGGDetect_Delta

open Filter Topology MeasureTheory

namespace RGGDetect

/-- **Theorem 2** (arXiv:2610.08517, held version, sha256 e7bebd4a…, Theorem 2, p.4, eq. (10)): in the
setting of Theorem 1, `KL(P_RGG∥P_ER) ≤ n′K ≤ n′Δ + o(1)`, with `n′ = n - 1`; consequently, to prove
Theorem 1 it suffices to prove `Δ = o(1/n)`.

**Formalization Note** Sequences `p, d, τ` in the regime (1) (`Regime`). `K` is `rowK`, `Δ` is `Delta`
with slack `B* = B`; the statement is for every `B`. The `o(1)` is a sequence `e → 0` chosen after the
sequences. The "consequently" clause is the third conjunct: `n Δ_n → 0` implies `KL → 0`. -/
theorem theorem_2 (δ : ℝ) (hδ : 0 < δ) (B : ℕ) (p : ℕ → ℝ) (d : ℕ → ℕ) (τ : ℕ → ℝ)
    (hR : Regime δ p d τ) :
    (∀ᶠ n in atTop, InformationTheory.klDiv (rggLaw n (d n) (τ n)) (erLaw n (p n)) ≤
        ((n - 1 : ℕ) : ENNReal) * rowK n (d n) (τ n)) ∧
    (∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        ((n - 1 : ℕ) : ENNReal) * rowK n (d n) (τ n) ≤
          ENNReal.ofReal (((n - 1 : ℕ) : ℝ) * Delta n (d n) (τ n) B + e n)) ∧
    (Tendsto (fun n : ℕ => (n : ℝ) * Delta n (d n) (τ n) B) atTop (𝓝 0) →
      Tendsto (fun n => InformationTheory.klDiv (rggLaw n (d n) (τ n)) (erLaw n (p n)))
        atTop (𝓝 0)) := by sorry

end RGGDetect
