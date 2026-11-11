-- Prove2me | Theorems.Thm_SumReLU_lemma_4_13
-- name    : SumReLU.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:22.26279+00:00
-- url     : https://prove2.me/theorems/5fc3236e-c606-458d-bbca-5d2853fb68d4
-- title:
--   Lemma 4.13 — the complex Gaussian probe lands in $E^{\mathrm{Cor}}_{i^*}\cap E^{\mathrm{Sep}}_{i^*}$ with probability $\ge\mathrm{poly}(\lambda/k)$
-- statement:
--   Let $\xi\in(0,1/300]$. There are constants $c,C>0$ (depending only on $\xi$) such that the following holds for all $d,k$, every $\lambda\in(0,\sqrt\xi/10]$, all unit vectors $w_1,\dots,w_k\in\mathbb R^d$ and every $i^*\in[k]$. Let $p=\lceil\log(k/\lambda)/\log(1+\xi)\rceil$, $Z_p(\mathcal U)=p!$, and let $u=p+iq$ with $p,q$ independent $N(0,I_d)$. Then
--   $$
--   \Pr_{u\sim\mathcal U}\big[E^{\mathrm{Cor}}_{i^*}\cap E^{\mathrm{Sep}}_{i^*}\big]\ge C\Big(\frac{\lambda}{k}\Big)^c ,
--   $$
--   where $E^{\mathrm{Cor}}_{i^*}=\{|w_{i^*}\cdot u|\ge(p!)^{1/(2p)}\}$ and $E^{\mathrm{Sep}}_{i^*}=\{|w_{i^*}\cdot u|\ge(1+\xi)|w_j\cdot u|\ \forall j\in A_{i^*}(\xi)\}$.
--
--   Together with Lemma 4.2 this shows that polynomially many random probes suffice to find every heavy hidden vector.
--
--   **Formalization Note** $\lambda\le\sqrt\xi/10$ is the standing assumption of Section 4 (p.24). The two events are closed sets, so the probability is a genuine measure value.
--
--   Differences from the source:
--   - encoding: $\ge\mathrm{poly}(\lambda/k)$ → $\ge C(\lambda/k)^c$ for some $c,C>0$; reason: §2, p.9: "$g(t)\ge\mathrm{poly}(t)$ for $t<1$: there exist constants $c,C>0$ such that $g(t)\ge Ct^c$"
--   - reading: constants of $\mathrm{poly}$, with $\xi$ "a small absolute constant" → $c,C$ chosen after $\xi$ and before $d,k,\lambda,w,i^*$; reason: $\xi$ is fixed first; the proof's constants depend on $\xi$ only
--   - reading: $\lambda$ (not quantified in the lemma) → $\lambda\in(0,\sqrt\xi/10]$; reason: the standing assumption of Section 4, p.24 (PDF p.26)
--   - generalization: Section 4.3's standing assumption $k\le d$ (Remark 4.12, p.34: "Throughout this section, we assume without loss of generality that $k\le d$") → no relation between $d$ and $k$; reason: the bound does not depend on it (the lemma's statement involves only the law of the projections of the probe or of $(x,z)$, not the ambient dimension); the statement specializes to $k\le d$
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.13, p.34 (PDF p.36); Section 4 standing assumption, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_SumReLU_probeLaw
import Definitions.Def_SumReLU_events

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- **Lemma 4.13** (Probability of Successful Filtration).

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.13, p.34 (PDF p.36): "Let u = p + iq, where p, q iid∼ N(0, I_d). Let ξ ∈ (0, 1/300] be a
small absolute constant, p = ⌈log(k/λ)/log(1 + ξ)⌉ and Z_p(U) = p!. Let w_1, …, w_k be k unit vectors.
Fixing any i* ∈ [k], let A_{i*}(ξ) = {i ∈ [k] : |w_i · w_{i*}| ≤ 1 − ξ} and let the "correlation" and
"separation" events on U be defined by (11). Then, Pr_{u∼U}[E^{Cor}_{i*} ∩ E^{Sep}_{i*}] ≥ poly(λ/k)."

**Formalization Note.**
* `≥ poly(λ/k)` is read by §2, p.9 (PDF p.11): "g(t) ≥ poly(t) for a quantity t < 1 … there exist
  constants c, C > 0 such that g(t) ≥ Ct^c". The constants come after `ξ` ("a small absolute
  constant", fixed first) and before `d, k, λ, w, i*`.
* `λ ∈ (0, √ξ/10]` is the standing assumption of Section 4, p.24 (PDF p.26): "Throughout this
  section, we take … λ ≤ √ξ/10, where ξ is an absolute constant".
* Section 4.3's standing assumption `k ≤ d` (Remark 4.12, p.34, PDF p.36) is not imposed; the bound
  does not depend on it, and the statement specializes to `k ≤ d`.
* The two events are closed sets, so the probability is a genuine measure value. -/
theorem lemma_4_13 (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 300) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (d k : ℕ) (lam : ℝ), 0 < lam → lam ≤ Real.sqrt ξ / 10 →
      ∀ w : Fin k → EuclideanSpace ℝ (Fin d), (∀ i, ‖w i‖ = 1) → ∀ i₀ : Fin k,
        ENNReal.ofReal (C * (lam / k) ^ c) ≤
          probeLaw d (corrEvent w i₀ (degree ξ k lam) ((degree ξ k lam).factorial : ℝ) ∩
            sepEvent ξ w i₀) := by sorry

end SumReLU
