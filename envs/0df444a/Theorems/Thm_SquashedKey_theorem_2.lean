-- Prove2me | Theorems.Thm_SquashedKey_theorem_2
-- name    : SquashedKey.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:33:17.945842+00:00
-- url     : https://prove2.me/theorems/d359485d-55b6-485c-87fc-711a8e569bab
-- title:
--   Theorem 2 — $\log_2K\le E_{sq}(AA';BB')_\omega+f_1(\sqrt\varepsilon,K)$ whenever $F(\gamma,\omega)\ge1-\varepsilon$, for shields of any dimension
-- statement:
--   Let $\gamma_{AA'BB'}$ be a private state of $\log_2K$ private bits (definition (5)), where the key systems $A$, $B$ have dimension $K$ and the shields $A'$, $B'$ have arbitrary (possibly infinite) dimension. Let $\omega_{AA'BB'}$ be an $\varepsilon$-approximate private state, in the sense that
--   $$
--   F(\gamma_{AA'BB'},\omega_{AA'BB'})\ge1-\varepsilon
--   $$
--   for some $\varepsilon\in[0,1]$. Then
--   $$
--   \log_2K\le E_{sq}(AA';BB')_\omega+f_1(\sqrt\varepsilon,K),\qquad f_1(\varepsilon,K)=2\varepsilon\log_2K+2(1+\varepsilon)h_2\!\left(\frac{\varepsilon}{1+\varepsilon}\right).
--   $$
--
--   The correction $f_1(\sqrt\varepsilon,K)$ depends only on $\varepsilon$ and $K$, not on the dimension of the shields. This is what makes the bound applicable to key distillation in infinite-dimensional (for instance bosonic Gaussian) settings, where it yields that squashed entanglement bounds distillable key.
--
--   **Formalization Note** Hilbert spaces are $\ell^2$ of arbitrary index types; $F(\gamma,\omega)=\|\sqrt\gamma\sqrt\omega\|_1^2$ and $E_{sq}$ (an infimum over extensions on every system $E$ of the extended conditional mutual information in bits) take values in $[0,+\infty]$, so the hypothesis is `ENNReal.ofReal (1 - ε) ≤ F γ ω` and the conclusion an inequality in $[0,+\infty]$ with $\log_2K$ and $f_1(\sqrt\varepsilon,K)$ (both $\ge0$ for $K\ge1$, $\varepsilon\in[0,1]$) entered through `ENNReal.ofReal`.
--
--   Differences from the source:
--
--   - reading: I(A;B|E) = H(AE)+H(BE)−H(E)−H(ABE) (15), which is ∞ − ∞ when the entropies are infinite → Shirokov's extended conditional mutual information (published qcmi: supremum over finite-rank projectors P on A of I(PA;BE) − I(PA;E)) divided by ln 2, valued in ℝ≥0∞; reason: the paper allows infinite-dimensional shields and extensions and takes (21) from [Shi17], which is proved for this quantity; it equals (15) whenever the entropies in (15) are finite, so it changes no instance on which (15) is defined
--   - reading: γ 'is called a private state' if (5) holds for any purification; the twisted form (6) is 'a non-trivial consequence' → IsPrivateState γ: (5) holds for every unit vector φ on every purifying system E : Type with Tr_E |φ⟩⟨φ| = γ; reason: (5) is the definition printed on p.4; (6) is stated as a theorem of the mission (eq_6_twisted_form)
--   - encoding: Hilbert spaces of any dimension → ℓ²(I) for an arbitrary index type I (no finiteness or countability), operators as coefficient arrays, states as the published trace-class State I; reason: every Hilbert space has an orthonormal basis and is ℓ² of its index set; the same instances
--   - encoding: real-valued log₂ K and information quantities → information quantities in ℝ≥0∞, real terms entered through ENNReal.ofReal; reason: the quantities are nonnegative and may be +∞ in infinite dimension; ENNReal.ofReal of a nonnegative real is that real (log₂ K ≥ 0 for K ≥ 1, and for K = 0 there is no state)
--   - encoding: F(γ, ω) ≥ 1 − ε (44) with F a real number → ENNReal.ofReal (1 − ε) ≤ traceClassSquaredFidelity γ ω in ℝ≥0∞; reason: F(γ, ω) = ‖√γ√ω‖₁² is a finite nonnegative real and ENNReal.ofReal (1 − ε) = 1 − ε for ε ≤ 1; the same instances
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, Theorem 2, eqs. (44)–(46), p.8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P02
import Definitions.Def_SquashedKey_Information
import Definitions.Def_SquashedKey_KeyBoundFunction
import Definitions.Def_SquashedKey_PrivateState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Intakenext100.P02 (traceClassSquaredFidelity)

namespace SquashedKey

/-- **Theorem 2**, Wilde, *Squashed entanglement and approximate private states*,
arXiv:1606.08028v3, Theorem 2, (44)–(46), p.8 (PDF p.8): "Let `γ_{AA′BB′}` be a private state and
let `ω_{AA′BB′}` be an ε-approximate private state, in the sense that
`F(γ_{AA′BB′}, ω_{AA′BB′}) ≥ 1 − ε` (44) for `ε ∈ [0, 1]`. Then
`log₂ K ≤ E_sq(AA′; BB′)_ω + f₁(√ε, K)`, (45) where
`f₁(ε, K) ≡ 2ε log₂ K + 2(1 + ε)h₂(ε/[1 + ε])`. (46)"

For every `K`, all shield types `A′`, `B′` (any dimension, infinite included), every private state
`γ` (definition (5)) and every state `ω` on `(AA′)(BB′)`, and every `ε ∈ [0, 1]` with
`F(γ, ω) ≥ 1 − ε`: `log₂ K ≤ E_sq(AA′; BB′)_ω + f₁(√ε, K)`.

**Formalization Note** Hilbert spaces are `ℓ²` of arbitrary index types; the key systems are
`Fin K` with the standard basis. A private state is defined by (5) (`IsPrivateState`). `F` is the
squared fidelity `‖√γ √ω‖₁²` and `E_sq` the squashed entanglement (28), an infimum over extensions
on every system `E : Type`, of the extended conditional mutual information in bits; both are valued
in `ℝ≥0∞`, so (44) is `ENNReal.ofReal (1 − ε) ≤ F γ ω` and (45) is an inequality in `ℝ≥0∞` with
`ENNReal.ofReal` of the real numbers `log₂ K` and `f₁(√ε, K)` (both nonnegative for `K ≥ 1` and
`ε ∈ [0, 1]`). -/
theorem theorem_2 {K : ℕ} {A' B' : Type} (γ ω : State ((Fin K × A') × (Fin K × B')))
    (hγ : IsPrivateState γ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hF : ENNReal.ofReal (1 - ε) ≤ traceClassSquaredFidelity γ ω) :
    ENNReal.ofReal (Real.logb 2 (K : ℝ)) ≤
      squashedEntanglement ω + ENNReal.ofReal (f₁ (Real.sqrt ε) K) := by sorry

end SquashedKey
