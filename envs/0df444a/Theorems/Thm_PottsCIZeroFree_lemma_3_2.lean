-- Prove2me | Theorems.Thm_PottsCIZeroFree_lemma_3_2
-- name    : PottsCIZeroFree.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:04.573537+00:00
-- url     : https://prove2.me/theorems/be451e2e-be68-449a-a970-dba977cb1737
-- title:
--   Lemma 3.2 — positive-activity Potts induction: uniform zero-free discs around $[\delta,1]$ and the response bound (17)
-- statement:
--   Fix integers $q,\Delta$ with $q\ge1$ and $\Delta\ge2$, let $\delta\in(0,1]$ and $C\in[0,\infty)$. There are $\alpha,\varepsilon>0$, depending only on $(q,\Delta,\delta,C)$, with the following property. Let $\mathcal G\subseteq\mathcal G_\Delta$ be closed under taking induced subgraphs and satisfy $C$-coupling independence on $[\delta,1]$. Then for every $G\in\mathcal G$, every pinning $\tau$, every $x\in[\delta,1]$ and every $z\in\mathbb C$ with $|z-x|<\varepsilon$,
--   $$\widehat Z^\tau_G(z)\ne0,$$
--   and, for every $v\in V^\tau$ and $a,b\in[q]$,
--   $$\left|\operatorname{Log}\frac{\widehat Z^{\tau^{v=a}}_G(z)/\widehat Z^{\tau^{v=a}}_G(x)}{\widehat Z^{\tau^{v=b}}_G(z)/\widehat Z^{\tau^{v=b}}_G(x)}\right|\le\alpha,$$
--   the logarithm being continued from $z=x$.
--
--   This gives the zero-free region away from $z=0$: a disc of uniform radius around every point of $[\delta,1]$, for all graphs of the class at once.
--
--   **Formalization Note** The continued logarithm is a continuous function $g$ on the disc $|z-x|<\varepsilon$ with $g(x)=0$ whose exponential is the ratio; on a disc such a $g$ is unique. The constants $\alpha,\varepsilon$ are chosen before the class.
--
--   Differences from the source:
--   - encoding: a class 𝒢 of finite simple graphs → a predicate on graphs on Fin n for every n (GraphClass); reason: every finite graph is isomorphic to one on Fin n, Ẑ is invariant under relabeling, and a class closed under induced embeddings is closed under isomorphism
--   - encoding: colors [q] = {1, …, q} → Fin q = {0, …, q−1}; reason: relabeling of colors; every quantity is invariant under it
--   - encoding: a pinning τ : Λ → [q] → a set Λ ⊆ V with τ : V → Fin q, read only on Λ; reason: every pinning extends to such a τ and every definition ignores τ off Λ (proved in the sanity file)
--   - encoding: the logarithm of (17) continued from z = x → ∃ g continuous on the disc with g(x) = 0, exp ∘ g = ratio and ‖g‖ ≤ α; reason: the disc is connected and the ratio is continuous and nonvanishing there, so the continuous logarithm with g(x) = 0 is unique
--   - encoding: q, Δ positive integers (standing assumption of §2.1, p.7) → 0 < q (and 0 < Δ) as hypotheses; reason: the section’s standing assumption, copied into the binders
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.11 (PDF p.13), Lemma 3.2, display (17)

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_CouplingIndependent

open Classical

namespace PottsCIZeroFree

/-- Lemma 3.2 (Positive-activity Potts induction) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.11 (PDF p.13).
Fix integers `q, Δ` with `Δ ≥ 2`, `δ ∈ (0, 1]` and `C ∈ [0, ∞)`, and let `𝒢 ⊆ G_Δ` be closed
under taking induced subgraphs and satisfy `C`-coupling independence on `[δ, 1]`. There are
`α, ε > 0`, depending only on `(q, Δ, δ, C)`, such that for every `G ∈ 𝒢`, every pinning `τ`,
every `x ∈ [δ, 1]` and every `z` with `|z − x| < ε`, `Ẑ^τ_G(z) ≠ 0`, and for every `v ∈ V^τ`
and `a, b ∈ [q]`,
`|Log ((Ẑ^{τ^{v=a}}_G(z)/Ẑ^{τ^{v=a}}_G(x)) / (Ẑ^{τ^{v=b}}_G(z)/Ẑ^{τ^{v=b}}_G(x)))| ≤ α` (17),
the logarithm continued from `z = x`.

**Formalization Note.** `α, ε` are chosen before the class `𝒢`. The continued logarithm is a
continuous `g` on the disc `|z − x| < ε` with `g(x) = 0` and `exp ∘ g` equal to the ratio; the
disc is connected, so `g` is unique and is the logarithm of (17). `q` is positive (§2.1). -/
theorem lemma_3_2 (q Δ : ℕ) (hq : 0 < q) (hΔ : 2 ≤ Δ) (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ α ε : ℝ, 0 < α ∧ 0 < ε ∧
      ∀ 𝒢 : GraphClass, DegBounded 𝒢 Δ → ClosedInduced 𝒢 →
        CouplingIndependent q 𝒢 C (Set.Icc δ 1) →
        ∀ n (G : SimpleGraph (Fin n)), 𝒢 n G →
          ∀ (Λ : Set (Fin n)) (τ : Fin n → Fin q), ∀ x ∈ Set.Icc δ 1,
            (∀ z : ℂ, ‖z - x‖ < ε → (normPinnedPoly G Λ τ).eval z ≠ 0) ∧
            ∀ v, v ∉ Λ → ∀ a b : Fin q, ∃ g : ℂ → ℂ,
              ContinuousOn g (Metric.ball (x : ℂ) ε) ∧ g x = 0 ∧
              ∀ z ∈ Metric.ball (x : ℂ) ε,
                Complex.exp (g z) =
                  ((normPinnedPoly G (childSet Λ v) (childPin τ v a)).eval z / (normPinnedPoly G (childSet Λ v) (childPin τ v a)).eval (x : ℂ)) /
                ((normPinnedPoly G (childSet Λ v) (childPin τ v b)).eval z / (normPinnedPoly G (childSet Λ v) (childPin τ v b)).eval (x : ℂ)) ∧
                ‖g z‖ ≤ α := by sorry

end PottsCIZeroFree
