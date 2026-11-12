-- Prove2me | Theorems.Thm_WildeQIT_EntManip_theorem_19_4_1
-- name    : WildeQIT.EntManip.theorem_19_4_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T18:40:26.470979+00:00
-- url     : https://prove2.me/theorems/2ba22dc4-3bc7-44ce-82b4-4e3537fb441c
-- title:
--   Theorem 19.4.1 (Entanglement Manipulation): $E(\psi\to\varphi)=H(A)_\psi/H(A)_\varphi$
-- statement:
--   Let $|\psi\rangle_{AB},|\varphi\rangle_{AB}\in\mathcal H_A\otimes\mathcal H_B$ be pure bipartite states of finite-dimensional systems, with $H(A)_\varphi>0$. The entanglement manipulation limit for the conversion $|\psi\rangle_{AB}\to|\varphi\rangle_{AB}$ by LOCC is
--
--   $$
--   E(\psi\to\varphi)=\frac{H(A)_\psi}{H(A)_\varphi},
--   $$
--
--   where $E(\psi\to\varphi)$ is the supremum of the achievable rates: $E$ is achievable when for every $\varepsilon\in(0,1)$, $\delta>0$ and all sufficiently large $n$ there is an LOCC channel taking $\psi_{AB}^{\otimes n}$ to a state $\varepsilon$-close in normalized trace distance to $\varphi_{AB}^{\otimes m}$ with $m/n\ge E-\delta$.
--
--   The theorem says that pure-state entanglement is a single resource measured by the entropy of entanglement: concentration and dilution are each optimal, and asymptotic conversion between pure states is reversible.
--
--   **Formalization Note** Pure states are unit vectors on `a × b`. The conclusion is that $H(A)_\psi/H(A)_\varphi$ is the least upper bound of the set of achievable rates (`IsLUB`), which states both that the set is bounded above and that the ratio is its supremum. The LOCC class is that of §19.2 (finite compositions of one-way rounds); output copies live on $A^m$, $B^m$ indexed by `Fin m → a`, `Fin m → b`.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces H_A, H_B → complex matrices over finite index types a, b; reason: the book's standing setting; same instances
--   - encoding: E(ψ → φ) = H(A)ψ/H(A)φ for all pure ψ, φ → hypothesis 0 < H(A)φ; reason: the ratio is undefined when φ is a product state; only that case is excluded
--   - reading: an (n, E − δ, ε) protocol (rate m/n equal to E − δ) → m/n ≥ E − δ; reason: m and n are integers, so m/n = E − δ is impossible for irrational E − δ; the book's proofs (19.56)–(19.58) use rates converging to E
--   - encoding: E(ψ → φ) is the supremum of the achievable rates, equal to the ratio → IsLUB of the set of achievable rates at the ratio; reason: same statement, without the junk value of a real sSup
--   - generalization: §19.3 (p. 540) has Alice and Bob begin with copies of a pure bipartite, entangled state |ψ⟩AB → any unit vector ψ, product states included; reason: for product ψ the claim is that the limit is 0, which is true (LOCC cannot create entanglement), and for entangled ψ the statement is exactly the book's
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 19.4.1, (19.47), p. 541

import Mathlib
import Definitions.Def_WildeQIT_EntManip_entEntropy
import Definitions.Def_WildeQIT_EntManip_IsAchievableRate

namespace WildeQIT.EntManip

/-- **Theorem 19.4.1 (Entanglement Manipulation)** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, p. 541): "Let `|ψ⟩_{AB}, |φ⟩_{AB} ∈ H_A ⊗ H_B` be pure bipartite
states. The entanglement manipulation limit for the conversion `|ψ⟩_{AB} → |φ⟩_{AB}` is equal to
the ratio `H(A)_ψ/H(A)_φ`: `E(ψ → φ) = H(A)_ψ / H(A)_φ`." (19.47)

`E(ψ → φ)` is the supremum of the achievable rates (§19.3, p. 540); the conclusion says that
`H(A)_ψ / H(A)_φ` is the least upper bound of the set of achievable rates.

**Formalization Note** Pure states are unit vectors on `a × b` (finite index types). The
hypothesis `0 < H(A)_φ` excludes the case where the ratio is undefined (product `φ`). `IsLUB`
states both that the set of achievable rates is bounded above and that its supremum is the
ratio, so no junk value of a real `sSup` is involved. -/
theorem theorem_19_4_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ φ : a × b → ℂ) (hψ : ∑ z, ‖ψ z‖ ^ 2 = 1) (hφ : ∑ z, ‖φ z‖ ^ 2 = 1)
    (hφpos : 0 < entEntropy φ) :
    IsLUB {E : ℝ | IsAchievableRate ψ φ E} (entEntropy ψ / entEntropy φ) := by sorry

end WildeQIT.EntManip
