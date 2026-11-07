-- Prove2me | Theorems.Thm_QMCBeyondHK_claim_3_2
-- name    : QMCBeyondHK.claim_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:04.430204+00:00
-- url     : https://prove2.me/theorems/1ece3d11-47ec-4398-be56-a12503997b09
-- title:
--   Claim 3.2 — the half-swap $T$ permutes $\Pi_{\le\ell}$ up to sign: $\Gamma\circ T = \chi(\Gamma)\,\rho(\Gamma)$
-- statement:
--   Let $n \ge 1$, $\ell = \lceil 10\log_2 n\rceil$, and let $H = H_{j,k}$ and $G = H_{j',k'}$ be in $\Pi_{\le\ell}$. Let $i \in [d]$ be a coordinate with $(j_i,k_i) \ne (j'_i,k'_i)$ and $j_i \ge j'_i$, and let $T$ swap the two halves of $\operatorname{supp} h_{j_i,k_i}$ in coordinate $i$. Then
--
--   1. $T$ maps $[0,1)^d$ into itself and $T \circ T$ is the identity on $[0,1)^d$;
--   2. there are a map $\chi : \Pi_{\le\ell} \to \{-1,+1\}$ and an involution $\rho : \Pi_{\le\ell} \to \Pi_{\le\ell}$ such that
--   $$
--   \Gamma \circ T = \chi(\Gamma)\, \rho(\Gamma) \quad \text{on } [0,1)^d \text{ for every } \Gamma \in \Pi_{\le\ell}, \tag{10}
--   $$
--   and moreover $\chi(H) = -1$, $\rho(H) = H$, $\chi(G) = +1$, $\rho(G) = G$.
--
--   This is the first half of the symmetry argument proving that distinct low-order Haar discrepancies are uncorrelated.
--
--   Differences from the source:
--   - encoding: χ : Π≤ℓ → {−1, +1} and an involution ρ : Π≤ℓ → Π≤ℓ → functions on all Haar indices whose values on Π≤ℓ are ±1, lie in Π≤ℓ and satisfy ρ(ρ(Γ)) = Γ; reason: only the restrictions to Π≤ℓ are constrained; same content
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Claim 3.2, eq. (10), p.10 (PDF p.12), with the definition of T and 'Clearly, T is an involution' on the same page

import Mathlib
import Definitions.Def_QMCBeyondHK_lowOrder
import Definitions.Def_QMCBeyondHK_swapMap

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Claim 3.2, printed p.10 (PDF p.12) of arXiv:2609.10921 (sha256 bc273e88…). Context (proof of
Lemma 3.1.1, p.10): `H = H_{j,k}` and `G = H_{j',k'}` in `Π≤ℓ`, `i` a coordinate with
`(j_i, k_i) ≠ (j'_i, k'_i)` and `j_i ≥ j'_i`, and `T` the map swapping the two halves of
`supp h_{j_i,k_i}` in coordinate `i`. Then `T` is an involution of `[0,1)^d`, and there are
`χ : Π≤ℓ → {−1, +1}` and an involution `ρ : Π≤ℓ → Π≤ℓ` with `Γ ∘ T = χ(Γ) ρ(Γ)` for every
`Γ ∈ Π≤ℓ` (10); moreover `χ(H) = −1`, `ρ(H) = H`, `χ(G) = +1`, `ρ(G) = G`.

**Formalization Note** `ℓ = ⌈10 log₂ n⌉`. `χ` and `ρ` are functions on all Haar indices; only
their values on `Π≤ℓ` are constrained. (10) is an identity of functions on `[0,1)^d`. -/
theorem claim_3_2 (d n : ℕ) (H G : HaarIdx d) (hH : H ∈ lowOrder d (ell n))
    (hG : G ∈ lowOrder d (ell n)) (i : Fin d) (hi : (H.j i, H.k i) ≠ (G.j i, G.k i))
    (hji : G.j i ≤ H.j i) :
    (∀ x ∈ cube d, swapMap i (H.j i) (H.k i) x ∈ cube d ∧
      swapMap i (H.j i) (H.k i) (swapMap i (H.j i) (H.k i) x) = x) ∧
    ∃ χ : HaarIdx d → ℝ, ∃ ρ : HaarIdx d → HaarIdx d,
      (∀ Γ ∈ lowOrder d (ell n), (χ Γ = 1 ∨ χ Γ = -1) ∧ ρ Γ ∈ lowOrder d (ell n) ∧ ρ (ρ Γ) = Γ ∧
        ∀ x ∈ cube d, haar Γ (swapMap i (H.j i) (H.k i) x) = χ Γ * haar (ρ Γ) x) ∧
      χ H = -1 ∧ ρ H = H ∧ χ G = 1 ∧ ρ G = G := by sorry

end QMCBeyondHK
