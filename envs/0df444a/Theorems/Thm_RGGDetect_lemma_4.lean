-- Prove2me | Theorems.Thm_RGGDetect_lemma_4
-- name    : RGGDetect.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:39:56.963991+00:00
-- url     : https://prove2.me/theorems/32bfd19c-459b-45b0-806a-4ea42e8b7fc1
-- title:
--   Lemma 4 — Bayes rule for external edges
-- statement:
--   Let $u\in V$ and $I=V^c$. The second term of (29) can be re-expressed as
--
--   $$
--   \mathbb E\big[(\mathbb E[D\mid G_{-u},Y_I])^2\big]=\mathbb E\left[\int\frac{r_{u,I,D}(y)^2}{\Lambda_{u,I}(y)}\,dQ_I(y)\right], \tag{33}
--   $$
--
--   with the integrand interpreted as zero when $\Lambda_{u,I}=0$.
--
--   This rewrites the posterior moment as a ratio whose denominator is the external-edge likelihood ratio.
--
--   **Formalization Note** An exact identity for every $n,d$, every $\tau$ with $0<p<1$, every $V$ and $u\in V$, and every real function $D$ of the configuration.
--
--   Differences from the source:
--   - generalization: D ∈ H_ℓ (the standing D of §3) → every real function D of the configuration; reason: the identity is algebraic (Bayes rule on finitely many atoms); it specializes to D ∈ H_ℓ
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 4, eq. (33), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RGGDetect_cavity

namespace RGGDetect

/-- **Lemma 4** (Bayes rule for external edges; arXiv:2610.08517, held version, sha256 e7bebd4a…,
Lemma 4, p.13, eq. (33)): the second term of (29) can be re-expressed as
`E[(E[D | G_{-u}, Y_I])²] = E[∫ r_{u,I,D}(y)²/Λ_{u,I}(y) dQ_I(y)]`, `I = V^c`, with the integrand
interpreted as zero when `Λ_{u,I} = 0`.

**Formalization Note** An exact identity for every `n`, `d`, `τ` with `0 < p < 1`, `V`, `u ∈ V`, and
every real function `D` of the configuration (the paper states it for its `D ∈ H_ℓ`). Lean's
`x/0 = 0` is the paper's convention for the integrand. -/
theorem lemma_4 (n d : ℕ) (τ : ℝ) (hp0 : 0 < capProb d τ) (hp1 : capProb d τ < 1)
    (V : Finset (Fin n)) (u : Fin n) (hu : u ∈ V) (D : Config n d → ℝ) :
    postMoment (fun x => (graphMinus τ u x, rowY τ u Vᶜ x)) D =
      cavInt n d τ u Vᶜ D (fun _ _ => True) := by sorry

end RGGDetect
