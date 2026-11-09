-- Prove2me | Theorems.Thm_OuterplanarL1Tan_Linear_lemma_6
-- name    : OuterplanarL1Tan.Linear.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:15:41.12762+00:00
-- url     : https://prove2.me/theorems/72a04ba3-c6ec-4d97-94bc-4f0c4ba4caa5
-- title:
--   Lemma 6 — exact norms with simultaneous localization bounds
-- statement:
--   Let $X$ be any finite set, and let $\delta(x,y)=\|f(x)-f(y)\|_1$ for a map $f$ into real summable sequences. Let $h:X\to[0,\infty)$ be arbitrary. There exist a finite dimension $N$ and a single deterministic map $\Psi:X\to\ell_1^N$ such that simultaneously for every $x,y\in X$,
--
--   $$\|\Psi(x)\|_1=h(x),$$
--   $$\|\Psi(x)-\Psi(y)\|_1\le\delta(x,y)+3|h(x)-h(y)|,$$
--   $$\|\Psi(x)-\Psi(y)\|_1\ge\tfrac14\min\{\delta(x,y),\max\{h(x),h(y)\}\}.$$
--
--   No positivity, Lipschitz condition, bounded ratio or compatibility assumption is placed on $h$. In particular distinct points of zero $\delta$-distance may have different prescribed norms. Empty and singleton sets are permitted. The result supplies all three properties for the component maps used in the general embedding theorem.
--
--   **Formalization Note** The ℓ₁ input is encoded by existence of an actual map into the full `lp` sequence space, with no finite-support assumption. The finite input domain is explicit in the preamble to Lemma 6. The finite output realization is justified by the source's coordinate-merging paragraph on printed p.6. The cut decomposition is a proof obligation, not an added hypothesis.
--
--   Differences from the source:
--   - encoding: a finite ℓ₁ metric δ on X → a real function δ with an actual full-sequence ℓ₁ realization and a Fintype X; reason: this spells out the source preamble without assuming the finite cut decomposition
--   - generalization: an ℓ₁ metric → an ℓ₁ pullback pseudometric without injectivity; reason: all metric instances are retained and §3.3 requires pullbacks that may identify vertices; h remains arbitrary on each zero-distance class
--   - generalization: an output in ℓ₁ → a finite dimension N and an output in PiLp 1 over Fin N; reason: the source proof gives finitely many coordinates; padding with zeros recovers summable real sequences without changing any norm; this implies the source’s ℓ₁ conclusion
-- source:
--   Zihan Tan, Improved Embedding of k-Outerplanar Metrics into ℓ₁, STOC 2027 submission #262 (October 2026), p. 5–6, Lemma 6, equations (1)–(3), and finite-X preamble (PDF p. 6–7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/262.pdf; SHA256 0ec64e77e85f536fdf7dc42bb8fdeedaf8861f751861d02b2d5edbdef75ee0ab

import Definitions.Def_OuterplanarL1Tan_Linear_L1Distance
import Definitions.Def_OuterplanarL1Tan_Linear_BoundaryPattern

namespace OuterplanarL1Tan.Linear

/-- Lemma 6, printed pp.5–6 (PDF pp.6–7), all three conclusions.
The preamble explicitly says finite distances; output finite dimension is
established in the coordinate-merging paragraph on printed p.6.
The pseudometric generalization allows distinct zero-distance points to have
different prescribed norms. Input sequences need not have finite support. -/
theorem lemma_6 {X : Type} [Fintype X] (δ : X → X → ℝ)
    (isL1 : IsL1Distance δ) (h : X → ℝ) (nonnegative : ∀ x, 0 ≤ h x) :
    ∃ N : ℕ, ∃ Ψ : X → L1Vector N,
      (∀ x, ‖Ψ x‖ = h x) ∧
      (∀ x y, ‖Ψ x - Ψ y‖ ≤ δ x y + 3 * |h x - h y|) ∧
      (∀ x y, (1 / 4 : ℝ) * min (δ x y) (max (h x) (h y)) ≤
        ‖Ψ x - Ψ y‖) := by sorry

end OuterplanarL1Tan.Linear
