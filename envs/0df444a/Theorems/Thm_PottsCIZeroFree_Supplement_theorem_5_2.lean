-- Prove2me | Theorems.Thm_PottsCIZeroFree_Supplement_theorem_5_2
-- name    : PottsCIZeroFree.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:36:20.885232+00:00
-- url     : https://prove2.me/theorems/d7bb42f5-7b8a-439b-a79c-2dc06badcf6c
-- title:
--   Theorem 5.2 (Lee–Yang polydisc) — Potts color-field zero-freeness near $\lambda=\mathbf 1$ in three regimes
-- statement:
--   Let $q,\Delta$ be integers with $\Delta\ge2$. Write $\mathcal G_\Delta$ for the class of finite simple graphs of maximum degree at most $\Delta$ and, for $g\ge3$, $\mathcal G_{\Delta,g}$ for those graphs in $\mathcal G_\Delta$ of girth at least $g$ (an acyclic graph has girth $+\infty$). Each of the parameter assumptions
--
--   1. $q\ge(11/6-1/84000)\,\Delta$;
--   2. $\Delta\ge125$ and $q\ge1.809\,\Delta$;
--   3. $\Delta\ge3$ and $q\ge\Delta+3$
--
--   yields the following. In cases 1 and 2 put $\mathcal G=\mathcal G_\Delta$; in case 3 there is an integer $g_{\mathrm{LY}}=g_{\mathrm{LY}}(q,\Delta)\ge3$ for which $\mathcal G=\mathcal G_{\Delta,g_{\mathrm{LY}}}$. There is $\theta=\theta(q,\Delta)\in(0,1/2]$ such that, for every $G\in\mathcal G$ and every pinning $\tau:\Lambda\to[q]$ (proper or not),
--   $$\widehat Z^\tau_G(\lambda)\neq0\qquad\text{whenever }|\lambda_{u,c}-1|<\theta\quad(u\in V^\tau,\ c\in[q]),$$
--   where $\widehat Z^\tau_G(\lambda)$ is the normalized pinned field polynomial (38). If $\tau$ is proper on $G[\Lambda]$, then also the pinned field polynomial $Z^\tau_G(\lambda)\neq0$ under the same polydisc condition on $V^\tau\times[q]$ provided $\lambda_{v,\tau_v}\neq0$ for every $v\in\Lambda$; in particular $Z^\tau_G(\lambda)\neq0$ whenever $|\lambda_{u,c}-1|<\theta$ for every vertex $u\in V$ and every color $c\in[q]$.
--
--   This is the Lee–Yang analogue of the edge-activity theorem: zero-freeness in independent complex color fields around the uniform field, uniformly over the graph class and the pinning.
--
--   **Formalization Note** The three cases are the three conjuncts. $q,\Delta$ are natural numbers and the thresholds are real inequalities, with $1.809=1809/1000$. Girth is Mathlib's `SimpleGraph.egirth : ℕ∞`. $\theta$ (and $g_{\mathrm{LY}}$) are chosen after $(q,\Delta)$ and before the graph. The conclusion is the definition `PolydiscZeroFree`.
--
--   Differences from the source:
--   - encoding: girth$(G)\ge g$ with acyclic graphs of girth $+\infty$ → `(g : ℕ∞) ≤ G.egirth`, Mathlib's extended girth, which is `⊤` exactly for acyclic graphs; reason: same graphs.
--   - encoding: $q,\Delta$ integers, $q\ge1.809\Delta$ → `q Δ : ℕ`, `(1809/1000 : ℝ) * Δ ≤ q`; reason: every threshold forces $q,\Delta>0$, so no instance is lost.
--   - encoding: $\lambda\in\mathbb C^{V\times[q]}$, colors $[q]$ → `lam : V → Fin q → ℂ`, colors `Fin q`; reason: Lean convention, same instances.
--   - reading: "the corresponding statement for $Z^\tau_G(\lambda)$ follows from (39) provided $\lambda_{v,\tau_v}\neq0$" for a proper pinning → the conclusion clause "$Z^\tau_G(\lambda)\neq0$ whenever $|\lambda_{u,c}-1|<\theta$ on $V^\tau\times[q]$ and $\lambda_{v,\tau_v}\neq0$ on $\Lambda$", with the same $\theta$, and "proper pinning" read as proper on $G[\Lambda]$ (`pinnedMono G Λ τ = 0`); reason: this is what (39) yields and is the paper's usage of "proper on $G[\Lambda]$" (p.2, p.26).
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), Theorem 5.2, p.27 (PDF p.29); classes $\mathcal G_\Delta$, $\mathcal G_{\Delta,g}$ §2.1 p.7 (PDF p.9); (38)–(39) pp.25–26 (PDF pp.27–28)

import Mathlib
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_Supplement_fieldNormPinned

open Classical

namespace PottsCIZeroFree.Supplement

open PottsCIZeroFree

/-- Theorem 5.2 (Lee–Yang polydisc) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*,
arXiv:2610.12456 (PDF sha256 831a1633…), printed p.27 (PDF p.29). Let `q, Δ` be integers with
`Δ ≥ 2`. Under each of (i) `q ≥ (11/6 − 1/84000)Δ`; (ii) `Δ ≥ 125` and `q ≥ 1.809Δ`;
(iii) `Δ ≥ 3` and `q ≥ Δ + 3`, there is `θ = θ(q, Δ) ∈ (0, 1/2]` such that for every `G` in the
class `𝒢` and every pinning `τ`, `Ẑ^τ_G(λ) ≠ 0` whenever `|λ_{u,c} − 1| < θ` (`u ∈ V^τ`,
`c ∈ [q]`); for a proper pinning the same holds for `Z^τ_G(λ)` provided `λ_{v,τ_v} ≠ 0` on `Λ`,
in particular under the polydisc condition at every vertex and color. In cases (i), (ii)
`𝒢 = 𝒢_Δ` (maximum degree `≤ Δ`); in case (iii) `𝒢 = 𝒢_{Δ,g_LY}` for an integer
`g_LY = g_LY(q, Δ) ≥ 3` (maximum degree `≤ Δ` and girth `≥ g_LY`).

**Formalization Note.** The thresholds are real inequalities on the natural numbers `q, Δ`
(`1.809 = 1809/1000`). Girth is Mathlib's `SimpleGraph.egirth : ℕ∞`, which is `⊤` for acyclic
graphs, matching the paper's convention `girth = +∞` (§2.1, p.7). `θ` and `g_LY` are chosen
after `q, Δ` and before the graph. The conclusion is `PolydiscZeroFree`. -/
theorem theorem_5_2 (q Δ : ℕ) (hΔ : 2 ≤ Δ) :
    ((11 / 6 - 1 / 84000 : ℝ) * Δ ≤ q →
      ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
        PolydiscZeroFree q (fun {V} [Fintype V] (G : SimpleGraph V) => MaxDegLE G Δ) θ) ∧
    (125 ≤ Δ ∧ (1809 / 1000 : ℝ) * Δ ≤ q →
      ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
        PolydiscZeroFree q (fun {V} [Fintype V] (G : SimpleGraph V) => MaxDegLE G Δ) θ) ∧
    (3 ≤ Δ ∧ Δ + 3 ≤ q →
      ∃ gLY : ℕ, 3 ≤ gLY ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
        PolydiscZeroFree q
          (fun {V} [Fintype V] (G : SimpleGraph V) => MaxDegLE G Δ ∧ (gLY : ℕ∞) ≤ G.egirth) θ) := by sorry

end PottsCIZeroFree.Supplement
