-- Prove2me | Theorems.Thm_QTolTest1673_Unified_theorem_1_1
-- name    : QTolTest1673.Unified.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:32.276594+00:00
-- url     : https://prove2.me/theorems/85ff1fcf-2ac3-4cd0-b5de-414f35fb9b41
-- title:
--   Theorem 1.1 — unified nonadaptive tolerant quantum tester for $L_{n,k}$ and $J_{n,k}$ with $O((k+\ln(1/\delta))/\Gamma^2)$ queries
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $1\le k<n$, $0\le\varepsilon_1<\varepsilon_2<1/2$ and $0<\delta<1/3$, and write
--   $$\Gamma=(1-2\varepsilon_1)^2-(1-2\varepsilon_2).$$
--   If $\Gamma>0$, then each of the classes $L_{n,k}$ (Boolean functions $x\mapsto h(Ax)$ with $A\in\mathbb F_2^{k\times n}$, i.e. of Fourier dimension at most $k$) and $J_{n,k}$ ($k$-juntas) admits a nonadaptive tolerant quantum tester $\mathcal A$, fixed before the input, such that for every $f:\mathbb F_2^n\to\{\pm1\}$:
--
--   1. if $\operatorname{dist}(f,\mathcal C)\le\varepsilon_1$, then $\mathcal A$ accepts $f$ with probability at least $1-\delta$;
--   2. if $\operatorname{dist}(f,\mathcal C)\ge\varepsilon_2$, then $\mathcal A$ rejects $f$ with probability at least $1-\delta$;
--
--   and $\mathcal A$ makes at most
--   $$C\cdot\frac{k+\ln(1/\delta)}{\Gamma^2}$$
--   queries to the standard value oracle $O_f|x,b\rangle=|x,b\oplus(1-f(x))/2\rangle$.
--
--   The query bound does not depend on $n$; at fixed thresholds it is linear in $k$, and the same tester structure serves both properties. The postprocessing of the measurement outcomes is unrestricted.
--
--   Differences from the source:
--   - encoding: $f:\mathbb F_2^n\to\{\pm1\}$ → its bit function `BoolFn n` with $f=(-1)^{b_f}$ (`toSign`); reason: a bijection; the XOR oracle adds $b_f=(1-f)/2$; same instances
--   - encoding: query complexity $O((k+\ln(1/\delta))/\Gamma^2)$ → $\exists C>0$ before all parameters, and query count $\le C(k+\ln(1/\delta))/\Gamma^2$; reason: the proof (p. 19) uses one sufficiently large absolute constant, and the $O(\cdot)$ is uniform over all parameters
--   - encoding: there is a nonadaptive tolerant quantum tester → there are $m,w,T$, a frozen $T$-query algorithm $A$ with workspace `Fin w` and a decision rule $D$ such that `nonadaptiveTester m A D` ($m$ independent runs of $A$, then $D$ of the outcomes) is the tester; reason: exhibiting a tester of this nonadaptive shape implies the existence claimed; Algorithm 1 has this shape (p. 21)
--   - encoding: number of queries of the tester → `worstCaseQueries`, the largest number of oracle calls over all branches of the algorithm tree (here $mT$); reason: the honest query count of the built algorithm, the same on every input
--   - encoding: Accept / Reject → output `true` / `false` of the algorithm, with probabilities `outProb f true` / `outProb f false`; reason: a naming of the two outputs; same instances
--   - encoding: coordinates $[n]=\{1,\dots,n\}$ → `Fin n` = $\{0,\dots,n-1\}$; reason: index base only; same instances
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), source.pdf SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, Theorem 1.1, p. 6 (restated p. 20, proof pp. 20–21)

import Definitions.Def_QTolTest1673_Unified_Classes
import Definitions.Def_QTolTest1673_Unified_Tester

namespace QTolTest1673.Unified

open QAlgorithms FourierDimTesting102.Quantum

/-- Theorem 1.1, p. 6 (restated p. 20; unified quantum upper bound). There is an absolute
constant `C > 0` such that for all `1 ≤ k < n`, `0 ≤ ε₁ < ε₂ < 1/2` and `0 < δ < 1/3` with
`Γ = (1 − 2ε₁)² − (1 − 2ε₂) > 0`, each of `L_{n,k}` and `J_{n,k}` has a nonadaptive tolerant
quantum tester (thresholds `ε₁, ε₂`) with error probability at most `δ` on both promise sides
whose number of oracle queries is at most `C (k + ln(1/δ))/Γ²`. The tester (`m` runs of one
frozen query algorithm `A`, then a decision rule `D`) is chosen before the input `f`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, 1 ≤ k → k < n →
        ∀ ε₁ ε₂ δ : ℝ, 0 ≤ ε₁ → ε₁ < ε₂ → ε₂ < 1 / 2 → 0 < δ → δ < 1 / 3 →
          0 < (1 - 2 * ε₁) ^ 2 - (1 - 2 * ε₂) →
          (∃ (m w T : ℕ) (A : QueryAlg (V n) Bool (Fin w) T)
              (D : List ((V n × Bool) × Fin w) → Bool),
              ((worstCaseQueries (nonadaptiveTester m A D) : ℕ) : ℝ) ≤
                  C * ((k + Real.log (1 / δ)) / ((1 - 2 * ε₁) ^ 2 - (1 - 2 * ε₂)) ^ 2) ∧
                IsTolerantTester (nonadaptiveTester m A D) (linJunta n k) ε₁ ε₂ δ) ∧
            (∃ (m w T : ℕ) (A : QueryAlg (V n) Bool (Fin w) T)
              (D : List ((V n × Bool) × Fin w) → Bool),
              ((worstCaseQueries (nonadaptiveTester m A D) : ℕ) : ℝ) ≤
                  C * ((k + Real.log (1 / δ)) / ((1 - 2 * ε₁) ^ 2 - (1 - 2 * ε₂)) ^ 2) ∧
                IsTolerantTester (nonadaptiveTester m A D) (junta n k) ε₁ ε₂ δ) := by sorry

end QTolTest1673.Unified
