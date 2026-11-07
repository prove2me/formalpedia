-- Prove2me | Theorems.Thm_QMCBeyondHK_claim_3_3
-- name    : QMCBeyondHK.claim_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:19.193205+00:00
-- url     : https://prove2.me/theorems/edb7b53f-b2e7-45f6-871b-dea194fd8f7c
-- title:
--   Claim 3.3 — Haar-thinning commutes with $T$: $A'_t = T(A_t)$ and $\varphi'_t(\Gamma) = \chi(\Gamma)\varphi_t(\rho(\Gamma))$
-- statement:
--   In the setting of Claim 3.2 ($\varepsilon \in (0,1)$, $\ell = \lceil 10\log_2 n\rceil$, $H, G \in \Pi_{\le\ell}$, the coordinate $i$ and the map $T$), let $\chi, \rho$ satisfy (10): $\chi(\Gamma) = \pm 1$, $\rho(\Gamma) \in \Pi_{\le\ell}$, $\rho(\rho(\Gamma)) = \Gamma$ and $\Gamma \circ T = \chi(\Gamma)\rho(\Gamma)$ on $[0,1)^d$ for every $\Gamma \in \Pi_{\le\ell}$. Let $(x_t,\xi_t,y_t)$ be any input stream with $x_t, y_t \in [0,1)^d$, and consider the transformed run, executed with the same $\xi_t$ but with $Tx_t$ and $Ty_t$ in place of $x_t$ and $y_t$; write $A'_t, \varphi'_t$ for its retained lists and discrepancies. Then for every $t \in \{0,1,\dots,n\}$,
--   $$
--   A'_t = T(A_t) \quad\text{and}\quad \varphi'_t(\Gamma) = \chi(\Gamma)\,\varphi_t(\rho(\Gamma)) \ \text{ for every } \Gamma \in \Pi_{\le\ell}. \tag{11}
--   $$
--
--   Together with the measure-preservation of $T$ this shows that $\varphi_t(H)\varphi_t(G)$ and $-\varphi_t(H)\varphi_t(G)$ have the same law.
--
--   Differences from the source:
--   - generalization: the χ, ρ constructed in Claim 3.2 → any χ, ρ with χ = ±1, ρ an involution of Π≤ℓ, and (10) on the cube; reason: Claim 3.2 provides such a pair, and the claim and its proof use only these properties
--   - encoding: the transformed run of the random strategy → a deterministic identity for every input stream with samples in [0,1)^d; A_t a list and T(A_t) its pointwise image; reason: the claim holds sample path by sample path; the paper's samples lie in [0,1)^d
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Claim 3.3, eq. (11), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_QMCBeyondHK_haarRun
import Definitions.Def_QMCBeyondHK_swapMap

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Claim 3.3, printed p.11 (PDF p.13) of arXiv:2609.10921 (sha256 bc273e88…). In the context of
Claim 3.2 (`H, G ∈ Π≤ℓ`, coordinate `i`, map `T`, and `χ, ρ` satisfying (10)), consider the
transformed run, executed with the same `ξ_t` but with `Tx_t` and `Ty_t` in place of `x_t` and `y_t`.
For every `t ∈ {0, 1, …, n}`, `A'_t = T(A_t)` and, for every `Γ ∈ Π≤ℓ`, `φ'_t(Γ) = χ(Γ) φ_t(ρ(Γ))` (11).

**Formalization Note** Deterministic, for every input stream with samples in `[0,1)^d`; `A_t` is the
list of retained points and `T(A_t)` its pointwise image. `χ, ρ` range over all pairs with the
properties Claim 3.2 provides. -/
theorem claim_3_3 (d : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ) (H G : HaarIdx d)
    (hH : H ∈ lowOrder d (ell n)) (hG : G ∈ lowOrder d (ell n)) (i : Fin d)
    (hi : (H.j i, H.k i) ≠ (G.j i, G.k i)) (hji : G.j i ≤ H.j i)
    (χ : HaarIdx d → ℝ) (ρ : HaarIdx d → HaarIdx d)
    (hχρ : ∀ Γ ∈ lowOrder d (ell n), (χ Γ = 1 ∨ χ Γ = -1) ∧ ρ Γ ∈ lowOrder d (ell n) ∧
      ρ (ρ Γ) = Γ ∧ ∀ x ∈ cube d, haar Γ (swapMap i (H.j i) (H.k i) x) = χ Γ * haar (ρ Γ) x)
    (xs : ℕ → Fin d → ℝ) (ξs : ℕ → ℝ) (ys : ℕ → Fin d → ℝ)
    (hxs : ∀ t, xs t ∈ cube d) (hys : ∀ t, ys t ∈ cube d) (t : ℕ) (ht : t ≤ n) :
    haarRun d ε (ell n) (fun u => swapMap i (H.j i) (H.k i) (xs u)) ξs
        (fun u => swapMap i (H.j i) (H.k i) (ys u)) t
      = (haarRun d ε (ell n) xs ξs ys t).map (swapMap i (H.j i) (H.k i)) ∧
    ∀ Γ ∈ lowOrder d (ell n),
      disc (haarRun d ε (ell n) (fun u => swapMap i (H.j i) (H.k i) (xs u)) ξs
          (fun u => swapMap i (H.j i) (H.k i) (ys u)) t) Γ
        = χ Γ * disc (haarRun d ε (ell n) xs ξs ys t) (ρ Γ) := by sorry

end QMCBeyondHK
