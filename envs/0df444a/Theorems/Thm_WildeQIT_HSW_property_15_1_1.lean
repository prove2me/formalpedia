-- Prove2me | Theorems.Thm_WildeQIT_HSW_property_15_1_1
-- name    : WildeQIT.HSW.property_15_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T19:12:12.045921+00:00
-- url     : https://prove2.me/theorems/9f7b9e5e-c8d8-479f-b201-40db3915fef6
-- title:
--   Property 15.1.1 (Unit Probability): $\mathrm{Tr}\{\Pi^\delta_{A^n}\rho^{\otimes n}\} \ge 1-\varepsilon$ for large $n$
-- statement:
--   Let $\rho_A$ be a density operator on a finite-dimensional Hilbert space $\mathcal H_A$ with spectral decomposition
--
--   $$
--   \rho_A = \sum_x p_X(x)\,|x\rangle\langle x|_A ,
--   $$
--
--   where $\{|x\rangle\}$ is an orthonormal eigenbasis and the eigenvalues $p_X(x)$ form a probability distribution, and let $\Pi^\delta_{A^n}$ be the $\delta$-typical projector built from this decomposition. Then for all $\varepsilon\in(0,1)$, $\delta>0$ and all sufficiently large $n$,
--
--   $$
--   \mathrm{Tr}\{\Pi^\delta_{A^n}\,\rho_A^{\otimes n}\} \ \ge\ 1-\varepsilon .
--   $$
--
--   In words, the typical subspace measurement of $n$ copies of $\rho$ finds the state in the typical subspace with probability approaching one. This is the first of the typical-subspace conditions verified when the packing lemma is applied in the direct part of the classical capacity theorem.
--
--   **Formalization Note** The spectral decomposition is given by its data: the columns of a unitary matrix and a probability distribution $p$; the statement holds for every such decomposition of $\rho$, including every choice of eigenbasis inside a degenerate eigenspace. The typical projector uses the weakly typical set of Definition 14.2.3; the book states the property for either the weak or the strong notion. The trace is real and its real part is taken.
--
--   Differences from the source:
--   - reading: typical subspace with respect to either the weak or the strong notion (p. 464) → the weakly typical set of Definition 14.2.3 (WildeQIT.typicalSet); reason: the book leaves the notion open and states Property 15.1.1 for both; the weak notion is the one of Definition 14.2.3 that the typical projector cites
--   - encoding: spectral decomposition (15.2) of ρ → a unitary U and a distribution p with ρ = Σ_x p(x)|u_x⟩⟨u_x|, eigenbasis labelled by the index type of H_A; reason: these are exactly the data of a spectral decomposition, and the eigenbasis has dim H_A elements
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Property 15.1.1, (15.17), p. 467; Definitions 15.1.2–15.1.3, pp. 464–465

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_HolevoCQ_tensorPowMat
import Definitions.Def_WildeQIT_Schumacher_typicalProjector

open Filter

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 15.1.1
(Unit Probability), p. 467: "Suppose that we perform a typical subspace measurement of a state
ρ_{Aⁿ}. Then the probability that the quantum state ρ_{Aⁿ} is in the typical subspace T^δ_{Aⁿ}
approaches one as n becomes large. That is, Tr{Π^δ_{Aⁿ} ρ_{Aⁿ}} ≥ 1 − ε, (15.17) for all
ε ∈ (0, 1), δ > 0, and sufficiently large n, where Π^δ_{Aⁿ} is the typical subspace projector
from Definition 15.1.3."

**Formalization Note.** The state is `ρ_{Aⁿ} = ρ_A^{⊗n}` (15.5), the published `HolevoCQ.tensorPowMat ρ n`,
and `ρ_A = Σ_x p_X(x)|x⟩⟨x|` (15.2) is a spectral decomposition given by its data: an
orthonormal eigenbasis, the columns of a unitary `U`, and eigenvalues forming a probability
distribution `p` (any such decomposition, including any choice of eigenbasis in a degenerate
eigenspace). These data make `ρ` a density operator. `Π^δ_{Aⁿ}` is
`WildeQIT.Schumacher.typicalProjector U p n δ`, built on the weakly typical set (Definition 14.2.3).
"Sufficiently large n" is `∀ᶠ n in atTop`; the trace is real here and its real part is taken. -/
theorem property_15_1_1 {A : Type} [Fintype A] [DecidableEq A]
    (ρ U : Matrix A A ℂ) (p : WildeQIT.FinDist A) (hU : U ∈ Matrix.unitaryGroup A ℂ)
    (hspec : ρ = ∑ x, ((p.prob x : ℝ) : ℂ) •
      Matrix.vecMulVec (fun a => U a x) (star (fun a => U a x)))
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ (Matrix.trace (WildeQIT.Schumacher.typicalProjector U p n δ * HolevoCQ.tensorPowMat ρ n)).re := by sorry

end WildeQIT.HSW
