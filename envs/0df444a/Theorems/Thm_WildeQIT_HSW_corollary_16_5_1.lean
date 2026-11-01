-- Prove2me | Theorems.Thm_WildeQIT_HSW_corollary_16_5_1
-- name    : WildeQIT.HSW.corollary_16_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T19:12:44.978925+00:00
-- url     : https://prove2.me/theorems/30e654e4-65b8-4d5a-a385-d80dd3a615d8
-- title:
--   Corollary 16.5.1 (derandomized packing lemma): a code with $\mathrm{Tr}\{\Lambda_m\sigma_{c_m}\} \ge 1 - 4(\varepsilon+2\sqrt\varepsilon) - 16|\mathcal M|d/D$
-- statement:
--   Let $\{p_X(x),\sigma_x\}_{x\in\mathcal X}$ be an ensemble of density operators on a finite-dimensional Hilbert space $\mathcal H$, indexed by a finite set $\mathcal X$, with expected density operator $\sigma \equiv \sum_x p_X(x)\sigma_x$. Suppose that $\Pi$ (the code subspace projector) and $\{\Pi_x\}_{x\in\mathcal X}$ (the codeword subspace projectors) are projectors on $\mathcal H$ such that, for every $x\in\mathcal X$,
--
--   1. $\mathrm{Tr}\{\Pi\sigma_x\}\ge 1-\varepsilon$,
--   2. $\mathrm{Tr}\{\Pi_x\sigma_x\}\ge 1-\varepsilon$,
--   3. $\mathrm{Tr}\{\Pi_x\}\le d$,
--
--   and
--
--   4. $\Pi\sigma\Pi \le \frac1D\Pi$ (operator inequality),
--
--   where $\varepsilon\in(0,1)$ and $d\in(0,D)$. Let $\mathcal M$ be a finite nonempty set of messages. Then there exist codewords $c_m\in\mathcal X$, $m\in\mathcal M$, and a POVM $\{\Lambda_m\}_{m\in\mathcal M}$ such that
--
--   $$
--   \mathrm{Tr}\{\Lambda_m\sigma_{c_m}\} \ \ge\ 1 - 4\bigl(\varepsilon+2\sqrt\varepsilon\bigr) - 16\,|\mathcal M|\,\frac dD \qquad\text{for every } m\in\mathcal M .
--   $$
--
--   The bound is useful when $\varepsilon$ is small and $|\mathcal M|\ll D/d$. In the direct part of the classical capacity theorem it is applied with typical and conditionally typical projectors, giving codes of rate close to $I(X;B)$ with small maximal error.
--
--   **Formalization Note** Projectors are Hermitian idempotent matrices; the operator inequality is positive semidefiniteness of $\frac1D\Pi - \Pi\sigma\Pi$; traces are real here and their real parts are taken. The message set is assumed nonempty, because a POVM needs at least one outcome.
--
--   Differences from the source:
--   - reading: "M is a set of size |M| with elements m" → a nonempty finite type; reason: on the empty set no POVM exists (an empty sum is not I), so the book's set of messages is nonempty
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 16.5.1, (16.70)–(16.74), p. 496; Definition 16.2.1, (16.2), p. 487

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QMemory_IsPOVM
import Definitions.Def_WildeQIT_HSW_IsProjector

open scoped ComplexOrder

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Corollary 16.5.1,
p. 496 (derandomized packing lemma), for the ensemble of Definition 16.2.1, p. 487
(`{p_X(x), σ_x}_{x∈𝒳}`, `σ_x ∈ D(H)`, expected density operator `σ ≡ Σ_x p_X(x) σ_x` (16.2)):
"Suppose that a code subspace projector Π and codeword subspace projectors {Π_x}_{x∈𝒳} exist,
they project onto subspaces of H, and these projectors and the ensemble have the following
properties: Tr{Πσ_x} ≥ 1 − ε, (16.70) Tr{Π_xσ_x} ≥ 1 − ε, (16.71) Tr{Π_x} ≤ d, (16.72)
ΠσΠ ≤ (1/D)Π, (16.73) where ε ∈ (0, 1) and d ∈ (0, D). Suppose that M is a set of size |M| with
elements m. Then there exists a code C₀ = {c_m}_{m∈M} with codewords c_m depending on the message
m and taking values in 𝒳, and there exists a corresponding POVM {Λ_m}_{m∈M} that reliably
distinguishes the states {σ_{c_m}}_{m∈M} in the sense that the probability of detecting the
correct state is high: ∀m ∈ M Tr{Λ_mσ_{c_m}} ≥ 1 − 4(ε + 2√ε) − 16|M| d/D, (16.74)".

**Formalization Note.** `H` is a finite index type, `𝒳` a finite type `X`, `p_X` a published
`WildeQIT.FinDist X`. Conditions (16.70)–(16.72) hold for every `x ∈ 𝒳`. Projectors are
`WildeQIT.HSW.IsProjector`; the operator inequality (16.73) is positive semidefiniteness of
`(1/D)Π − ΠσΠ`. The message set `M` is a nonempty finite type (on an empty set there is no
POVM, since an empty sum is not `I`). Traces are real here; real parts are taken. The book's
closing phrase "if ε is small and |M| ≪ D/d" is commentary on when the bound is useful, not a
hypothesis. -/
theorem corollary_16_5_1 {H X : Type} [Fintype H] [DecidableEq H] [Fintype X]
    (p : WildeQIT.FinDist X) (σ : X → Matrix H H ℂ) (hσ : ∀ x, WildeQIT.IsDensityOperator (σ x))
    (P : Matrix H H ℂ) (Px : X → Matrix H H ℂ) (hP : IsProjector P)
    (hPx : ∀ x, IsProjector (Px x))
    (ε d D : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 < d) (hdD : d < D)
    (h70 : ∀ x, 1 - ε ≤ (Matrix.trace (P * σ x)).re)
    (h71 : ∀ x, 1 - ε ≤ (Matrix.trace (Px x * σ x)).re)
    (h72 : ∀ x, (Matrix.trace (Px x)).re ≤ d)
    (h73 : (((1 / D : ℝ) : ℂ) • P - P * (∑ x, ((p.prob x : ℝ) : ℂ) • σ x) * P).PosSemidef)
    (M : Type) [Fintype M] [Nonempty M] :
    ∃ (c : M → X) (Λ : M → Matrix H H ℂ), WildeQIT.QMemory.IsPOVM Λ ∧
      ∀ m, 1 - 4 * (ε + 2 * Real.sqrt ε) - 16 * (Fintype.card M : ℝ) * d / D ≤
        (Matrix.trace (Λ m * σ (c m))).re := by sorry

end WildeQIT.HSW
