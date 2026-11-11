-- Prove2me | Theorems.Thm_QNoiseStab_theorem_3_5
-- name    : QNoiseStab.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:48.347491+00:00
-- url     : https://prove2.me/theorems/da2da167-86c9-41d1-882f-8123ea789508
-- title:
--   Theorem 3.5 — Quantum Noise Stability Bound
-- statement:
--   Let $X$ be a finite set, $\hat Y$ any set, $R\subseteq X^n\times\hat Y$ a relation, $A\subseteq[n]$, $p\in(0,1)$ and $E_{\mathrm{free}}\subseteq X^n$. For every $y\in\hat Y$ let $E_y=\{x\in X^n\setminus E_{\mathrm{free}}:(x,y)\in R\}$. Consider any quantum query algorithm making $T\le n$ phase queries to an input $x$ chosen uniformly at random from $X^n$, and let $\mathrm{succ}$ be the probability that it outputs a $y\in\hat Y$ with $(x,y)\in R$. Then
--
--   $$
--   \mathrm{succ}\ \le\ 2(1-p)^{-T}\max_{y\in\hat Y}\max_{x\in E_y}\Pr\bigl[N_p^A(x)\in E_y\bigr]+\frac{2|E_{\mathrm{free}}|}{|X|^n},
--   $$
--
--   and when $E_{\mathrm{free}}=\emptyset$ the bound tightens to
--
--   $$
--   \mathrm{succ}\ \le\ (1-p)^{-T}\max_{y\in\hat Y}\max_{x\in E_y}\Pr\bigl[N_p^A(x)\in E_y\bigr].
--   $$
--
--   The theorem reduces upper bounds on the success probability of quantum query algorithms on uniform inputs to the purely classical question of how stable the events $E_y$ are under random resampling of coordinates. It is the tool behind the paper's time-space tradeoff lower bounds for hashing, sorting and matrix-vector products.
--
--   **Formalization Note** The input alphabet carries a bijection $\mathrm{enc}:X\to\mathbb Z_d$; the algorithm is the published `QAlgorithms.QueryAlg` (query register $[n]$, phase register $\mathbb Z_d$, any finite workspace) with phase oracle $\omega^{p\,\mathrm{enc}(x_i)}$ for any $\omega$ with $\omega^d=1$; the maxima are encoded by a bound $\beta\ge0$. Both clauses are stated, the second without the factor 2.
--
--   Differences from the source:
--   - encoding: $\max_{y\in\hat Y}\max_{x\in E_y}\Pr[N_p^A(x)\in E_y]$ → any $\beta\ge0$ with $\Pr[N_p^A(x)\in E_y]\le\beta$ for all $y$ and $x\in E_y$; reason: the maximum (with $\max\emptyset=0$) is such a $\beta$ and both bounds increase with $\beta$; no finiteness of $\hat Y$ is needed
--   - encoding: $X$ with "a bijective map v between X and [d]" (p.6) → `enc : X ≃ ZMod d`, universally quantified; reason: the residues $0,\dots,d-1$ replace $[d]$; $d=|X|$ follows from the bijection
--   - generalization: $\omega_d$ "some fixed d'th root of unity" (p.6) → any $\omega$ with $\omega^d=1$; reason: covers every fixed root the source may mean, including the primitive one
--   - encoding: initial state $|0\rangle_{QPW}$ followed by $U_0$ → the published `QueryAlg` with an arbitrary input-independent unit `start`; reason: the two give the same class of algorithms
--   - generalization: output $q(w)$ of the measured workspace $W$ → output `out` of the measured registers $QPW$; reason: the proof measures $QPW$ (p.14); $q(w)$ is the case `out = q ∘ Prod.snd`
--   - generalization: $E_{\mathrm{free}}\subset X^n$ → `Efree : Finset (Fin n → X)`, any subset; reason: adds only $E_{\mathrm{free}}=X^n$, where the bound (a) is at least 2
--   - encoding: "the probability that a quantum query algorithm … given an input chosen uniformly at random … produces a y such that (x, y) ∈ R" → `successProb`: the average over $x\in X^n$ of the probability of a correct output; reason: equals $\|\Pi^R_{\mathrm{succ}}|\psi_T\rangle\|^2$ for the purified uniform input (pp.6, 13)
--   - encoding: $(1-p)^{-T}$, $p\in(0,1)$ → `((1 - p) ^ T)⁻¹`, `p ∈ Set.Ioo 0 1`; reason: $1-p>0$
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Theorem 3.5, p.13 (proof pp.13–15)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QNoiseStab_successProb
import Definitions.Def_QNoiseStab_noiseProb
import Definitions.Def_QNoiseStab_eventSet

namespace QNoiseStab

/-- **Theorem 3.5** (Quantum Noise Stability Bound; Beame–Holman–Kornerup, *A Noise Operator
Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334
(version of 2026-11-02, sha256 814fe20e…), p.13). Let `R ⊆ Xⁿ × Ŷ`, `A ⊆ [n]`, `p ∈ (0, 1)`,
`E_free ⊆ Xⁿ`, and for every `y ∈ Ŷ` let `E_y` be the set of `x ∈ Xⁿ ∖ E_free` with `(x, y) ∈ R`.
Then the probability that a quantum query algorithm making `T ≤ n` queries, given an input chosen
uniformly at random from `Xⁿ`, produces a `y` with `(x, y) ∈ R` is at most
`2 (1 − p)^{-T} max_{y∈Ŷ} max_{x∈E_y} Pr[N_p^A(x) ∈ E_y] + 2 |E_free| / |X|ⁿ`;
when `E_free = ∅` the bound can be tightened to
`(1 − p)^{-T} max_{y∈Ŷ} max_{x∈E_y} Pr[N_p^A(x) ∈ E_y]`.

**Formalization Note**
* `X` is any finite type with a bijection `enc : X ≃ ZMod d` (the paper's `v : X → [d]`, p.6); the
  algorithm is the published `QAlgorithms.QueryAlg` with query register `Fin n`, phase register
  `ZMod d` and any finite workspace `W`, querying the phase oracle `phaseQuery ω (enc ∘ x)` for any
  `ω` with `ω ^ d = 1`. Its start state is an arbitrary input-independent unit vector (the paper's
  `|0⟩_{QPW}` followed by `U_0` gives the same class).
* The output is `out` of the measured `QPW` registers (the paper's `q(w)` is `out = q ∘ Prod.snd`).
* The success probability is `successProb`, the average over the uniform input of the probability
  of a correct output.
* `max_{y∈Ŷ} max_{x∈E_y} Pr[N_p^A(x) ∈ E_y]` is encoded by any `β ≥ 0` bounding all these
  probabilities (the maximum is such a `β`, with `max ∅ = 0`; both bounds increase with `β`).
* `(1 − p)^{-T}` is `((1 − p)^T)⁻¹`. Both clauses are stated; clause (b) carries no factor `2`. -/
theorem theorem_3_5 {X Ŷ W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
    {n d T : ℕ} [NeZero d] (enc : X ≃ ZMod d) (ω : ℂ) (hω : ω ^ d = 1)
    (R : Set ((Fin n → X) × Ŷ)) (A : Finset (Fin n)) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (Efree : Finset (Fin n → X)) (hT : T ≤ n) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T)
    (out : (Fin n × ZMod d) × W → Ŷ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ∀ y : Ŷ, ∀ x ∈ eventSet Efree R y, noiseProb p A x (eventSet Efree R y) ≤ β) :
    successProb enc ω alg out R ≤
        2 * ((1 - p) ^ T)⁻¹ * β + 2 * (Efree.card : ℝ) / (Fintype.card X : ℝ) ^ n ∧
      (Efree = ∅ → successProb enc ω alg out R ≤ ((1 - p) ^ T)⁻¹ * β) := by sorry

end QNoiseStab
