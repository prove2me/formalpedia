-- Prove2me | Theorems.Thm_QMCBeyondHK_lemma_3_1_1
-- name    : QMCBeyondHK.lemma_3_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:08.316808+00:00
-- url     : https://prove2.me/theorems/e8ed5129-ac00-4899-adeb-ef5e46641a8c
-- title:
--   Lemma 3.1.1 — uncorrelated Haar discrepancies: $\mathbb E[\varphi_t(H)\varphi_t(G)] = 0$ for distinct $H,G \in \Pi_{\le\ell}$
-- statement:
--   Let $d \ge 1$, $\varepsilon \in (0,1)$, $n \ge 1$, $\ell = \lceil 10\log_2 n\rceil$, and run the Haar-thinning strategy on an independent uniform input stream. For every $t \in \{0,1,\dots,n\}$ and every two distinct Haar functions $H, G \in \Pi_{\le\ell}$, the product $\varphi_t(H)\varphi_t(G)$ is integrable and
--   $$
--   \mathbb E\big[\varphi_t(H)\, \varphi_t(G)\big] = 0 .
--   $$
--
--   This is the paper's key new ingredient: it makes the second moment of the low-order error a diagonal quadratic form in the discrepancies.
--
--   Differences from the source:
--   - encoding: E[φ_t(H) φ_t(G)] → a Bochner integral, with the integrability of the product asserted as a conclusion; reason: rules out a junk value 0 for a non-integrable integrand
--   - generalization: the algorithm's own randomness (i.i.d. uniform samples and coins) → any probability space carrying measurable, mutually independent inputs with the uniform laws (IsStreamInput); reason: the canonical product space is one such space (proved in the sanity file); every statement about the law of the run specializes to it
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Lemma 3.1.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QMCBeyondHK_haarRun
import Definitions.Def_QMCBeyondHK_IsStreamInput

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Lemma 3.1.1 (Uncorrelated Haar discrepancies), printed p.9 (PDF p.11) of arXiv:2609.10921
(sha256 bc273e88…): for every `t ∈ {0, 1, …, n}` and every two distinct Haar functions
`H, G ∈ Π≤ℓ`, `E[φ_t(H) φ_t(G)] = 0`, for the Haar-thinning strategy with `ℓ = ⌈10 log₂ n⌉`.

**Formalization Note** The product is stated to be integrable, so the Bochner integral is not a
junk value. -/
theorem lemma_3_1_1 (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (hn : 1 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ) (hin : IsStreamInput P X Ξ Y)
    (t : ℕ) (ht : t ≤ n) (H G : HaarIdx d) (hH : H ∈ lowOrder d (ell n))
    (hG : G ∈ lowOrder d (ell n)) (hHG : H ≠ G) :
    Integrable (fun ω => disc (haarRun d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t) H *
      disc (haarRun d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t) G) P ∧
    ∫ ω, disc (haarRun d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t) H *
      disc (haarRun d ε (ell n) (X · ω) (Ξ · ω) (Y · ω) t) G ∂P = 0 := by sorry

end QMCBeyondHK
