-- Prove2me | Theorems.Thm_SquashedKey_eq_32_chain_rule
-- name    : SquashedKey.eq_32_chain_rule
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:54.199583+00:00
-- url     : https://prove2.me/theorems/8521ba30-b774-41e3-874f-799a2fc2b186
-- title:
--   Eq. (32) — two chain rules: $I(AA';BB'|E)=I(A;BB'|E)+I(A';BB'|AE)=I(A;BB'|E)+I(A';B'|AE)+I(A';B|B'AE)$
-- statement:
--   For every state $\rho$ on $AA'BB'E$ (key systems $A,B$ of dimension $K$; shields $A',B'$ and $E$ of arbitrary dimension),
--   $$
--   \begin{aligned}
--   I(AA';BB'|E)_\rho&=I(A;BB'|E)_\rho+I(A';BB'|AE)_\rho\\
--   &=I(A;BB'|E)_\rho+I(A';B'|AE)_\rho+I(A';B|B'AE)_\rho .
--   \end{aligned}
--   $$
--
--   These are two applications of the chain rule for conditional mutual information. The paper uses them for the extension $\gamma_{AA'BB'E}$ of a private state in the proof of Lemma 1, and again for $\omega_{AA'BB'E}$ in step (51) of the proof of Theorem 2.
--
--   **Formalization Note** All quantities are the extended conditional mutual information in bits, in $[0,+\infty]$, so the identities are sums with no subtraction. $I(A';B|B'AE)$ is computed with the conditioning registers grouped as $(A,B'),E$, the same quantity as $I(A';B|AB'E)$ in (31).
--
--   Differences from the source:
--
--   - generalization: γ_{AA′BB′E}, an extension of a private state → every state ρ on the five registers AA′BB′E; reason: the identities are the chain rule, which the paper applies to any state (also to ω in (51)); the paper's case is the instance ρ = γ_{AA′BB′E}
--   - reading: I(A;B|E) = H(AE)+H(BE)−H(E)−H(ABE) (15), which is ∞ − ∞ when the entropies are infinite → Shirokov's extended conditional mutual information (published qcmi: supremum over finite-rank projectors P on A of I(PA;BE) − I(PA;E)) divided by ln 2, valued in ℝ≥0∞; reason: the paper allows infinite-dimensional shields and extensions and takes (21) from [Shi17], which is proved for this quantity; it equals (15) whenever the entropies in (15) are finite, so it changes no instance on which (15) is defined
--   - encoding: Hilbert spaces of any dimension → ℓ²(I) for an arbitrary index type I (no finiteness or countability), operators as coefficient arrays, states as the published trace-class State I; reason: every Hilbert space has an orthonormal basis and is ℓ² of its index set; the same instances
--   - encoding: conditioning system written B′AE in (32) and AB′E in (31) → one grouping (A,B′),E for both; reason: the order of the conditioning registers is a relabelling of indices and does not change the quantity
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, eq. (32), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_SquashedKey_FiveParty

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

namespace SquashedKey

/-- **Two applications of the chain rule, (32)**, Wilde, *Squashed entanglement and approximate
private states*, arXiv:1606.08028v3, proof of Lemma 1, (32), p.7 (PDF p.7): "the following identity
holds as a consequence of two applications of the chain rule for conditional quantum mutual
information: `I(AA′; BB′|E)_γ = I(A; BB′|E)_γ + I(A′; BB′|AE)_γ
= I(A; BB′|E)_γ + I(A′; B′|AE)_γ + I(A′; B|B′AE)_γ`."

For every state `ρ` on `AA′BB′E` (any shields `A′`, `B′` and any system `E`):
`I(AA′; BB′|E) = I(A; BB′|E) + I(A′; BB′|AE)` and
`I(AA′; BB′|E) = I(A; BB′|E) + I(A′; B′|AE) + I(A′; B|AB′E)`.

**Formalization Note** The identities are stated for every state on the five registers, not only
for extensions of private states; the paper applies (32) to `γ` and, at (51), to `ω`. All
quantities are the extended conditional mutual information in bits, in `ℝ≥0∞`, so the identities are
sums with no subtraction. `I(A′; B|B′AE)` is the same quantity as `I(A′; B|AB′E)` of (31)
(`infoAp_B_ABpE`, conditioning registers grouped `(A, B′), E`). -/
theorem eq_32_chain_rule {K : ℕ} {A' B' E : Type} (ρ : State (FiveParty K A' B' E)) :
    infoAAp_BBp_E ρ.coefficients = infoA_BBp_E ρ.coefficients + infoAp_BBp_AE ρ.coefficients ∧
      infoAAp_BBp_E ρ.coefficients =
        infoA_BBp_E ρ.coefficients + infoAp_Bp_AE ρ.coefficients +
          infoAp_B_ABpE ρ.coefficients := by sorry

end SquashedKey
