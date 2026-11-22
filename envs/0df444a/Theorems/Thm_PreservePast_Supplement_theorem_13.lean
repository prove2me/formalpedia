-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_13
-- name    : PreservePast.Supplement.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:38:02.438803+00:00
-- url     : https://prove2.me/theorems/4e34c88e-aed6-493d-ad31-f847e341180b
-- title:
--   Theorem 13 — from the source exponent to identification
-- statement:
--   Consider a sequence of identification experiments: $k$ independent records with known source $\mu$, a uniform independent query index, a query channel $P_x$, a reference law $Q$ and a measurable domain $\mathcal T$. Set $\ell=\ln k$, $s=1/\ell$, $g=\ell$. Suppose Lemma 13 applies to every region of $Q$-mass at most $g/k$, with the same domain $\mathcal T$ and nonnegative score-loss bound $b=O(\sqrt{\ell\ln\ell})$; let $U_0$ be a uniform upper bound on $P_x(A)$ for these regions and $x\in\mathcal T$. Let $\mathcal T$ have a measurable partition into $N\ge1$ cells with centres $c_j$ such that $D(P_x\|P_{c_j})\le b_U$ on cell $j$, and put $M_\ast=\lceil 2e^b\rceil$, $n_\ast=\lceil M_\ast\ell\rceil$, $t_\mu=\mu(\mathcal T)$, $U=\ln(N+1)$, $G=(U+\ln p_\mu(b+\ln2))_+$. Assume
--   $$t_\mu\to1,\qquad U\to\infty,\qquad b+\ln\ell=o(U),\qquad G=o(U),$$
--   $$b_U\le b,\qquad b_U=o(\sqrt\ell),\qquad \frac{i_X-\ell}{\sqrt{2\ell}}\Rightarrow N\Big(\frac{\tau}{2\sqrt2},1\Big),\qquad U_0=u+o(1),\qquad u=\Phi\Big(\frac{\tau}{2\sqrt2}\Big),$$
--   where $i_X=\ln\frac{dP_X}{dQ_\mu}(Z)$ uses the actual query marginal $Q_\mu$. Then:
--
--   1. $S^\ast=u+o(1)$;
--   2. $\mathcal H_{n_\ast}(b;\mu)=(1+o(1))U$;
--   3. for each fixed $0<S<u$, both $C_{\min}\in\{I_{\min},B_{\min}\}$ satisfy $C_{\min}(S)=\big(\tfrac Su+o(1)\big)\,k\,\mathcal H_{n_\ast}(b;\mu)/\ln2$;
--   4. there is a finite-width sequence with success $u-o(1)$ and width at most $(1+o(1))\,k\,\mathcal H_{n_\ast}(b;\mu)/\ln2$;
--   5. every protocol, with success $S$, satisfies the converse
--   $$I(X;M\mid R)\ \ge\ \frac{k}{\ln2}\Big[\frac{(S-e_0)_+}{U_0}A-\ln2\Big],\qquad A=\big(\mathcal H_{n_\ast}(b;\mu)-\ln(4/s)\big)_+,\quad e_0=s+g^{-1}+1-t_\mu .$$
--
--   All information and register costs are in bits; $\mathcal H$ is in nats.
--
--   **Formalization Note** $I_{\min}(S)$ and $B_{\min}(S)$ are the least information $I(X;M\mid R)$ and the least register width among protocols of success at least $S$. The predicate "Lemma 13 applies" and the objects $\mathcal H_n$, $p_\mu$, $G$ are those of `PreservePast.Supplement.logScoreExp`.
--
--   Differences from the source:
--   - generalization: a sequence of experiments as k → ∞ → a sequence indexed by n with k_n → ∞ and k_n ≥ 3; reason: contains the indexing by k; nothing in the statement depends on the indexing, and k ≥ 3 only makes 0 < s = 1/ln k < 1 as Lemma 13 requires
--   - reading: Suppose Lemma 13 applies to every region of Q-mass at most g/k, with the same domain 𝒯 and nonnegative score-loss bound b → there is one bound C ≥ D(P_x‖Q) on 𝒯 and, for every region A, the tail hypothesis of Lemma 13 holds at the threshold Γ_A = b − C + ln(s/(2Q(A))); reason: the page names neither C nor Γ; this is the weakest hypothesis under which Lemma 13 gives score loss b for every region, and it is implied by every choice of one pair (C, Γ) with C − ln(sk/(2g)) + Γ ≤ b (the form used in Appendix J.2), so the theorem is stated at its strongest
--   - encoding: records, queries and a channel P_x → standard Borel record and query spaces and a Markov kernel P; reason: so that I(X; M | R) and the likelihood ratio i_X are defined; a regularity convention that excludes only undefined cases
--   - encoding: (i_X − ℓ)/√(2ℓ) ⇒ N(τ/(2√2), 1) → the distribution functions converge at every point to Φ(t − τ/(2√2)); reason: equivalent to convergence in distribution because the limit is continuous
--   - encoding: a measurable partition of 𝒯 into N cells with centres → a measurable label map from the record space to N labels and a centre for each label, with the divergence bound on 𝒯; reason: the restriction of the label map to 𝒯 is the partition
--   - encoding: G = (U − h_Δ)₊ with h_Δ = −ln p_μ(Δ + ln 2) → (U + ln p)₊, and 0 when p = 0; reason: h_Δ = +∞ when the small-ball mass vanishes
--   - encoding: o(1) relations and C_min(S) = (S/u + o(1)) k𝓗/ln 2 → null sequences valid for all protocols from some index on; every protocol of success ≥ S has information and width ≥ (S/u − e)k𝓗/ln 2 and one protocol of success ≥ S has width and information ≤ (S/u + e)k𝓗/ln 2; reason: two-part form of a least cost; avoids junk values of infima
--   - encoding: the converse (160) → the same inequality in [0, ∞] with A possibly infinite, 0·∞ = 0, truncated subtraction, and 0 < U₀ assumed; reason: 𝓗 may be +∞; information is nonnegative; (156) assumes 0 < U
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 13, p.49 (PDF p.51), eqs. (157)–(160); Lemmas 13–14, pp.46–47 (PDF pp.48–49)

import Mathlib
import Definitions.Def_PreservePast_Supplement_IdProtocol
import Definitions.Def_PreservePast_Supplement_logScoreExp

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace PreservePast.Supplement

/-- **Theorem 13 (From the source exponent to identification).** P. Xu, *Information Required to
Preserve Past Learning*, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa),
Theorem 13, p.49 (PDF p.51), eqs. (157)–(160); Lemmas 13 and 14, pp.46–47 (PDF pp.48–49); the
experiment and (156) are in §H.3, p.48 (PDF p.50).

A sequence of identification experiments: `k` independent records of law `μ`, a uniform
independent query index, query channel `P_x`, reference law `Q`, domain `𝒯`. With `ℓ = ln k`,
`s = 1/ℓ`, `g = ℓ`: Lemma 13 applies to every region of `Q`-mass at most `g/k` with score-loss
bound `b = O(√(ℓ ln ℓ))`, `b ≥ 0`; `U₀` bounds `P_x(A)` for these regions and `x ∈ 𝒯`; `𝒯` has a
measurable partition into `N` cells with centres `c_j` and `D(P_x‖P_{c_j}) ≤ b_U` on cell `j`;
`M* = ⌈2e^b⌉`, `n* = ⌈M*ℓ⌉`, `U = ln(N+1)`, `G = (U + ln p_μ(b + ln 2))₊`; and (157)–(158) hold:
`t_μ = μ(𝒯) → 1`, `U → ∞`, `b + ln ℓ = o(U)`, `G = o(U)`, `b_U ≤ b`, `b_U = o(√ℓ)`,
`(i_X − ℓ)/√(2ℓ) ⇒ N(τ/(2√2), 1)`, `U₀ → u = Φ(τ/(2√2))`. Then `S* = u + o(1)`,
`𝓗_{n*}(b; μ) = (1 + o(1))U`, for each fixed `0 < S < u` both `I_min(S)` and `B_min(S)` equal
`(S/u + o(1)) k𝓗_{n*}(b; μ)/ln 2` (159), a finite-width sequence has success `u − o(1)` at cost
`(1 + o(1)) k𝓗_{n*}/ln 2`, and every protocol satisfies the converse (160).

**Formalization Note.** The sequence is indexed by `n`, with `k_n → ∞` and `k_n ≥ 3` (so that
`0 < s < 1`). Record and query spaces are standard Borel and `P` is a Markov kernel, so that the
log-likelihood ratio `i_X = ln(dP_X/dQ_μ)(Z)` (Mathlib's jointly measurable `Kernel.rnDeriv`
against the query marginal `Q_μ = ∫ P_x μ(dx)`) is a random variable. "Lemma 13 applies … with
score-loss bound `b`" is the predicate `CommonScoreApplies`. The partition is a measurable label
map `cell` on the record space (its restriction to `𝒯` is the partition; cells may be empty).
Convergence in distribution to the normal law is convergence of the distribution functions at
every point. `u > 0` holds automatically; `0 < U₀` is assumed as in (156). `𝓗_{n*}(b; μ)` is
`logScoreExp` (an extended real, in nats); `(1 + o(1))U` is a two-sided bound from some index
on; in (159) and the "all labels" clause its real part is used from some index on (it is finite
there by the previous clause). `I_min`, `B_min` are stated in two parts (every protocol of
success `≥ S`; one protocol of success `≥ S` with both costs below the bound). (160) is stated
for every index and every protocol, with `S` its success, in `ℝ≥0∞`:
`A = (𝓗_{n*} − ln(4/s))₊ ∈ [0, ∞]`, truncated subtraction, and `0 · ∞ = 0`. -/
theorem theorem_13 (X Z : ℕ → Type) [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    [∀ n, Nonempty (X n)] [∀ n, MeasurableSpace (Z n)] [∀ n, StandardBorelSpace (Z n)]
    (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (P : ∀ n, Kernel (X n) (Z n)) [∀ n, IsMarkovKernel (P n)]
    (Q : ∀ n, Measure (Z n)) [∀ n, IsProbabilityMeasure (Q n)]
    (k : ℕ → ℕ) (hk3 : ∀ n, 3 ≤ k n) (hk : Tendsto k atTop atTop)
    (T : ∀ n, Set (X n)) (hT : ∀ n, MeasurableSet (T n))
    (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hbO : b =O[atTop] fun n => Real.sqrt (Real.log (k n) * Real.log (Real.log (k n))))
    (hsel : ∀ n, CommonScoreApplies (μ n) (fun x => P n x) (Q n) (T n) (1 / Real.log (k n))
      (Real.log (k n) / k n) (b n))
    (U₀ : ℕ → ℝ) (hU₀pos : ∀ n, 0 < U₀ n)
    (hU₀ : ∀ (n : ℕ) (A : Set (Z n)), MeasurableSet A →
      Q n A ≤ ENNReal.ofReal (Real.log (k n) / k n) → ∀ x ∈ T n, P n x A ≤ ENNReal.ofReal (U₀ n))
    (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n) (cell : ∀ n, X n → Fin (N n)) (hcell : ∀ n, Measurable (cell n))
    (ctr : ∀ n, Fin (N n) → X n) (bU : ℕ → ℝ)
    (hcov : ∀ n, ∀ x ∈ T n,
      InformationTheory.klDiv (P n x) (P n (ctr n (cell n x))) ≤ ENNReal.ofReal (bU n))
    (htμ : Tendsto (fun n => (μ n (T n)).toReal) atTop (𝓝 1))
    (hU : Tendsto (fun n => Real.log ((N n : ℝ) + 1)) atTop atTop)
    (hbU : (fun n => b n + Real.log (Real.log (k n))) =o[atTop]
      fun n => Real.log ((N n : ℝ) + 1))
    (hG : (fun n => coverGap (Real.log ((N n : ℝ) + 1))
        (affinityMass (μ n) (fun x => P n x) (T n) (b n + Real.log 2))) =o[atTop]
      fun n => Real.log ((N n : ℝ) + 1))
    (hbUb : ∀ n, bU n ≤ b n)
    (hbUo : bU =o[atTop] fun n => Real.sqrt (Real.log (k n)))
    (τ : ℝ)
    (hclt : ∀ t : ℝ, Tendsto (fun n => ((μ n ⊗ₘ P n) {p : X n × Z n |
        (Real.log (Kernel.rnDeriv (P n) (Kernel.const (X n) ((μ n).bind (P n))) p.1 p.2).toReal -
          Real.log (k n)) / Real.sqrt (2 * Real.log (k n)) ≤ t}).toReal) atTop
      (𝓝 (stdNormalCdf (t - τ / (2 * Real.sqrt 2)))))
    (hU₀lim : Tendsto U₀ atTop (𝓝 (stdNormalCdf (τ / (2 * Real.sqrt 2))))) :
    Tendsto (fun n => idOptimum (μ n) (fun x => P n x) (k n)) atTop
        (𝓝 (stdNormalCdf (τ / (2 * Real.sqrt 2)))) ∧
    (∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      (((1 - e n) * Real.log ((N n : ℝ) + 1) : ℝ) : EReal) ≤
          logScoreExp (μ n) (fun x => P n x) (Q n) (T n)
            ⌈(⌈2 * Real.exp (b n)⌉₊ : ℝ) * Real.log (k n)⌉₊ (b n) ∧
        logScoreExp (μ n) (fun x => P n x) (Q n) (T n)
            ⌈(⌈2 * Real.exp (b n)⌉₊ : ℝ) * Real.log (k n)⌉₊ (b n) ≤
          (((1 + e n) * Real.log ((N n : ℝ) + 1) : ℝ) : EReal)) ∧
    (∀ S : ℝ, 0 < S → S < stdNormalCdf (τ / (2 * Real.sqrt 2)) →
      ∃ (e : ℕ → ℝ) (n₀ : ℕ), Tendsto e atTop (𝓝 0) ∧ ∀ n, n₀ ≤ n →
        (∀ π : StateProtocol (Fin (k n) → X n) (Z n) (Fin (k n)),
          S ≤ idSuccess (μ n) (fun x => P n x) π →
          ENNReal.ofReal ((S / stdNormalCdf (τ / (2 * Real.sqrt 2)) - e n) *
            (k n * (logScoreExp (μ n) (fun x => P n x) (Q n) (T n)
              ⌈(⌈2 * Real.exp (b n)⌉₊ : ℝ) * Real.log (k n)⌉₊ (b n)).toReal / Real.log 2)) ≤
            idInfo (μ n) π ∧
          ∀ B : ℕ, π.HasWidth B →
            (S / stdNormalCdf (τ / (2 * Real.sqrt 2)) - e n) *
              (k n * (logScoreExp (μ n) (fun x => P n x) (Q n) (T n)
                ⌈(⌈2 * Real.exp (b n)⌉₊ : ℝ) * Real.log (k n)⌉₊ (b n)).toReal / Real.log 2) ≤
              (B : ℝ)) ∧
        ∃ (π : StateProtocol (Fin (k n) → X n) (Z n) (Fin (k n))) (B : ℕ),
          π.HasWidth B ∧ S ≤ idSuccess (μ n) (fun x => P n x) π ∧
          (B : ℝ) ≤ (S / stdNormalCdf (τ / (2 * Real.sqrt 2)) + e n) *
            (k n * (logScoreExp (μ n) (fun x => P n x) (Q n) (T n)
              ⌈(⌈2 * Real.exp (b n)⌉₊ : ℝ) * Real.log (k n)⌉₊ (b n)).toReal / Real.log 2) ∧
          idInfo (μ n) π ≤ ENNReal.ofReal ((S / stdNormalCdf (τ / (2 * Real.sqrt 2)) + e n) *
            (k n * (logScoreExp (μ n) (fun x => P n x) (Q n) (T n)
              ⌈(⌈2 * Real.exp (b n)⌉₊ : ℝ) * Real.log (k n)⌉₊ (b n)).toReal / Real.log 2))) ∧
    (∃ (e : ℕ → ℝ) (n₀ : ℕ), Tendsto e atTop (𝓝 0) ∧ ∀ n, n₀ ≤ n →
      ∃ (π : StateProtocol (Fin (k n) → X n) (Z n) (Fin (k n))) (B : ℕ),
        π.HasWidth B ∧
        stdNormalCdf (τ / (2 * Real.sqrt 2)) - e n ≤ idSuccess (μ n) (fun x => P n x) π ∧
        (B : ℝ) ≤ (1 + e n) *
          (k n * (logScoreExp (μ n) (fun x => P n x) (Q n) (T n)
            ⌈(⌈2 * Real.exp (b n)⌉₊ : ℝ) * Real.log (k n)⌉₊ (b n)).toReal / Real.log 2)) ∧
    ∀ (n : ℕ) (π : StateProtocol (Fin (k n) → X n) (Z n) (Fin (k n))),
      ENNReal.ofReal (k n / Real.log 2) *
        (ENNReal.ofReal (max (idSuccess (μ n) (fun x => P n x) π -
            (1 / Real.log (k n) + 1 / Real.log (k n) + (1 - (μ n (T n)).toReal))) 0) *
          (logScoreExp (μ n) (fun x => P n x) (Q n) (T n)
            ⌈(⌈2 * Real.exp (b n)⌉₊ : ℝ) * Real.log (k n)⌉₊ (b n) -
              ((Real.log (4 * Real.log (k n)) : ℝ) : EReal)).toENNReal /
          ENNReal.ofReal (U₀ n) - ENNReal.ofReal (Real.log 2)) ≤
        idInfo (μ n) π := by sorry

end PreservePast.Supplement
