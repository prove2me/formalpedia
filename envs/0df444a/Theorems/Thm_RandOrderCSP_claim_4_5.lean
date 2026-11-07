-- Prove2me | Theorems.Thm_RandOrderCSP_claim_4_5
-- name    : RandOrderCSP.claim_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:42.414381+00:00
-- url     : https://prove2.me/theorems/a482ac7d-8db6-4219-b84d-8df73c12f45f
-- title:
--   Claim 4.5 — one-wise uniform encoding of a rational 1-consistent labeling
-- statement:
--   Let $\Psi_*=(G_*,f_*)$ be a CSP with arity $k\ge2$ and nonempty alphabet $\Sigma$, and let $D_*:\mathcal E_{G_*}\to\Delta(\Sigma^k)$ be 1-consistent with all probabilities rational. Write $v^j_\ell=M_{G_*}(j,\ell)$. Then there are an integer $q\ge2$, maps $\kappa_v:\mathbb Z_q\to\Sigma$ for each vertex $v$, and a coloring $\mathcal Y_*:\mathcal E_{G_*}\to\Delta_1(\mathbb Z_q^k)$ such that for every edge $j$,
--
--   $$z\sim\mathcal Y_*(j)\ \Longrightarrow\ (\kappa_{v^j_1}(z_1),\dots,\kappa_{v^j_k}(z_k))\sim D_*(j).$$
--
--   This converts an LP solution of an integrality gap instance into a DIHP gadget together with decoding maps.
--
--   Differences from the source:
--   - generalization: a fixed gap instance Ψ∗ and a rational optimal LP solution D∗ → every instance and every rational 1-consistent D; reason: optimality and the gap are not used; the source case is an instance
--   - encoding: Σ a finite set → [Nonempty Sig]; reason: an isolated vertex needs a map κ_v into Σ; the source maximizes over assignments into Σ
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Claim 4.5, p.18

import Mathlib
import Definitions.Def_RandOrderCSP_IsOneWiseUniform

namespace RandOrderCSP

/-- **Claim 4.5** ([FMW26a, Proof of Lemma 3.1]). Singer, Tulsiani, Velusamy, *A dichotomy theorem for
approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256 3aca9d2f…),
Claim 4.5, p.18.

**Formalization Note.** The context of p.18 is an instance `Ψ*` and a 1-consistent `D*` with rational
probabilities; the claim is stated for all such pairs (optimality of `D*` is not used). `k ≥ 2` is the
standing arity of §3.3 and `[Nonempty Sig]` the alphabet's implicit nonemptiness: an isolated vertex
needs a map `κ_v : ℤ_q → Σ`. "`κ_j(z) ∼ D*(j)` for `z ∼ 𝒴*(j)`" is the pushforward identity. -/
theorem claim_4_5 {k : ℕ} (hk : 2 ≤ k) {Sig V E : Type} [Fintype Sig] [DecidableEq Sig] [Nonempty Sig]
    [Fintype V] [Fintype E] (Ψ : CSP k Sig V E) (D : E → (Fin k → Sig) → ℝ)
    (hD : IsOneConsistent Ψ D) (hrat : ∀ j x, ∃ r : ℚ, D j x = r) :
    ∃ (q : ℕ) (_ : NeZero q), 2 ≤ q ∧ ∃ (κ : V → ZMod q → Sig) (Y : E → (Fin k → ZMod q) → ℝ),
      (∀ j, IsOneWiseUniform (Y j)) ∧
      ∀ j (a : Fin k → Sig),
        ∑ z : Fin k → ZMod q, (if (fun ℓ => κ (Ψ.H.M j ℓ) (z ℓ)) = a then Y j z else 0) = D j a := by sorry

end RandOrderCSP
