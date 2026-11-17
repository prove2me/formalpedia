-- Prove2me | Theorems.Thm_RobustKellyTV_Supplement_theorem_B_1
-- name    : RobustKellyTV.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:32:30.459216+00:00
-- url     : https://prove2.me/theorems/bc69ef72-df53-437c-9615-6e1279539513
-- title:
--   Theorem B.1 — finite-sample regret of the oracle mixture
-- statement:
--   Assume the standing assumptions: $d\ge2$, $P_i>0$ for every $i$, and $0<\epsilon_0<1-\min_iP_i$; the null is $\mathcal P_0=B_{\mathrm{TV}}(P,\epsilon_0)$. For $m,\delta>0$ let
--
--   $$\mathcal K_{m,\delta}=\{U\in\Delta_d:\ \min_iU_i\ge m,\ D_{\mathrm{TV}}(U,P)\ge\epsilon_0+\delta\}.$$
--
--   Let $\mathcal A\subset\Delta_d\setminus\mathcal P_0$ be compact and contained in some $\mathcal K_{m,\delta}$ with $m,\delta>0$, and let $\Pi$ be a probability measure with full support on $\mathcal A$ ($\Pi(\mathcal A)=1$ and every relatively open nonempty subset of $\mathcal A$ has positive mass). Let $B^\Pi_n=\int_{\mathcal A}\prod_{t=1}^nE_U(X_t)\,\Pi(dU)$ be the oracle mixture (53), $\Gamma(S)=\inf_{R\in\mathcal P_0}D_{\mathrm{KL}}(S\|R)$, and $h(S,U)=\sum_iS_i\log E_U(i)$. Then:
--
--   1. $(B^\Pi_n)$ is a test supermartingale under the conditionally varying null.
--   2. Fix a full-support $S\in\mathcal A$ and let $X_1,X_2,\dots$ be i.i.d. from $S$. For every measurable $V\subseteq\mathcal A$ with $\Pi(V)>0$ and every $n$, $\log B^\Pi_n$ is integrable and
--
--   $$0\le n\Gamma(S)-\mathbb E_S\log B^\Pi_n\le\log\frac1{\Pi(V)}+n\sup_{U\in V}\{\Gamma(S)-h(S,U)\}\le\log\frac1{\Pi(V)}+n\sup_{U\in V}D_{\mathrm{KL}}(S\|U).$$
--
--   The mixture over pointwise oracles is thus valid against an adaptively varying null, never grows faster in expectation than the oracle rate $\Gamma(S)$, and loses at most the log-inverse prior mass of a neighbourhood $V$ plus $n$ times the worst oracle mismatch over $V$; choosing $V$ a small ball around $S$ gives logarithmic regret (Corollary B.2).
--
--   **Formalization Note** Observations are coordinates of $\omega:\mathbb N\to\mathrm{Fin}\,d$ under the i.i.d. law of $S$; $\mathbb E_S$ is a Bochner integral and integrability of $\log B^\Pi_n$ is part of the conclusion. Both suprema are taken in the extended reals, with $D_{\mathrm{KL}}$ valued in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: test supermartingale under the conditionally varying null (undefined in the paper) → M_0 = 1, M ≥ 0, and a supermartingale for the prefix filtration under every probability law on sequences whose one-step conditional laws lie in P0 almost surely; reason: the standard sequential composite null, the strongest natural reading, and the one the paper's proof (each fixed-U factor is in E0, then Tonelli) establishes
--   - encoding: Π with full support on A → Π a probability measure with Π(A) = 1 and every relatively open nonempty subset of A of positive Π-mass; reason: the definition of the support of a measure on the compact set A
--   - encoding: i.i.d. observations X_1, X_2, … from S → the infinite product law of S on ℕ → Fin d, with X_t the coordinate t − 1; reason: every process is a function of the observed prefix, so no instance changes
--   - encoding: E_S log B^Π_n → Bochner integral, with integrability of log B^Π_n added as a conjunct of the conclusion; reason: rules out the junk value 0 of a non-integrable integral; log B^Π_n is bounded on A ⊆ K_{m,δ}, so this adds no content beyond the paper's
--   - encoding: real suprema over V and log(1/Π(V)) → suprema in EReal (D_KL in [0, ∞], coerced), log(1/Π(V)) as Real.log (1 / Π(V).toReal); reason: no junk value of a real supremum; both suprema are finite on A ⊆ K_{m,δ}, and Π(V) ∈ (0, 1]
--   - encoding: n unspecified → every n ∈ ℕ, including n = 0; reason: at n = 0, B^Π_0 = 1 and the chain reads 0 ≤ 0 ≤ log(1/Π(V)), which holds, so no instance changes
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, Appendix B, Theorem B.1, eq. (54), p.35 (proof p.36); setting of Appendix B, p.35; K_{m,δ}, p.22

import Mathlib
import Definitions.Def_RobustKellyTV_kl
import Definitions.Def_RobustKellyTV_oracleE
import Definitions.Def_RobustKellyTV_seqLaw
import Definitions.Def_RobustKellyTV_Supplement_oracleMixture
import Definitions.Def_RobustKellyTV_Supplement_IsTestSupermartingaleCV

open MeasureTheory
open scoped ENNReal

namespace RobustKellyTV.Supplement

/-- **Theorem B.1** (Finite-sample regret of the oracle mixture). A. Saha, A. Ramdas, *Beyond
least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing*,
arXiv:2611.02130v1, Appendix B, Theorem B.1, eq. (54), p.35 (proof p.36).

Let `A ⊂ ∆_d \ P0` be compact, contained in some `K_{m,δ}`, and let `Π` be a probability measure
with full support on `A`. The process `(B^Π_n)` is a test supermartingale under the conditionally
varying null. Fix a full-support `S ∈ A`. For every measurable `V ⊆ A` with `Π(V) > 0`,
`0 ≤ nΓ(S) − E_S log B^Π_n ≤ log(1/Π(V)) + n sup_{U∈V} {Γ(S) − h(S, U)}
  ≤ log(1/Π(V)) + n sup_{U∈V} D_KL(S‖U)`.

**Formalization Note.** Standing assumptions (p.6) are bundled in `σ : Setting d`.
`K_{m,δ} = {U ∈ ∆_d : minᵢ Uᵢ ≥ m, D_TV(U, P) ≥ ϵ0 + δ}` (p.22) is written out, with
`minᵢ Uᵢ ≥ m` as `∀ i, m ≤ Uᵢ`. "Full support on `A`": `Π(A) = 1` and every relatively open
nonempty subset of `A` has positive mass. `E_S` is the Bochner integral under the i.i.d. law of
`S` on `ℕ → Fin d`, and integrability of `log B^Π_n` is a conjunct, so a junk value `0` cannot
satisfy the bounds. Both suprema are taken in the extended reals (`EReal`; `D_KL` is `[0, ∞]`-valued
and coerced), so no junk value of a real supremum enters; `n` ranges over all of `ℕ`. -/
theorem theorem_B_1 {d : ℕ} (σ : Setting d) (A : Set (Fin d → ℝ)) (hAc : IsCompact A)
    (hAnull : A ⊆ stdSimplex ℝ (Fin d) \ nullBall σ)
    (hAK : ∃ m δ : ℝ, 0 < m ∧ 0 < δ ∧
      A ⊆ {U | U ∈ stdSimplex ℝ (Fin d) ∧ (∀ i, m ≤ U i) ∧ σ.ε₀ + δ ≤ tv U σ.P})
    (prior : Measure (Fin d → ℝ)) [IsProbabilityMeasure prior] (hprior : prior A = 1)
    (hsupp : ∀ O : Set (Fin d → ℝ), IsOpen O → (O ∩ A).Nonempty → 0 < prior (O ∩ A)) :
    IsTestSupermartingaleCV σ (oracleMixture σ prior A) ∧
    ∀ S : stdSimplex ℝ (Fin d), (S : Fin d → ℝ) ∈ A → (∀ i, 0 < (S : Fin d → ℝ) i) →
    ∀ V : Set (Fin d → ℝ), MeasurableSet V → V ⊆ A → 0 < prior V → ∀ n : ℕ,
      Integrable (fun ω => Real.log (oracleMixture σ prior A n ω)) (seqLaw S) ∧
      0 ≤ (n : ℝ) * Gamma σ S - ∫ ω, Real.log (oracleMixture σ prior A n ω) ∂(seqLaw S) ∧
      (((n : ℝ) * Gamma σ S - ∫ ω, Real.log (oracleMixture σ prior A n ω) ∂(seqLaw S) : ℝ) :
          EReal) ≤
        ((Real.log (1 / (prior V).toReal) : ℝ) : EReal) +
          (n : EReal) * (⨆ U ∈ V, ((Gamma σ S - hRet σ S U : ℝ) : EReal)) ∧
      ((Real.log (1 / (prior V).toReal) : ℝ) : EReal) +
          (n : EReal) * (⨆ U ∈ V, ((Gamma σ S - hRet σ S U : ℝ) : EReal)) ≤
        ((Real.log (1 / (prior V).toReal) : ℝ) : EReal) +
          (n : EReal) * ((⨆ U ∈ V, kl S U : ℝ≥0∞) : EReal) := by sorry

end RobustKellyTV.Supplement
