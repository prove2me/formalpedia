-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_claim_4_2
-- name    : PDynTreeEmbed.Main.claim_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:32:03.037826+00:00
-- url     : https://prove2.me/theorems/afe8a6a4-8cf5-4c5a-98eb-e511c8582278
-- title:
--   Claim 4.2 — touching is necessary, covering is sufficient, a touching center covers with probability ≥ e⁻²
-- statement:
--   Fix a connected graph with integer weights in $[1,W]$ on $n\ge2$ vertices, a level $0<\ell<L$ with $D=2^\ell$, and a valid execution of Algorithm 2 with parameter $D$. Let $Z\subseteq V$ be nonempty with $\mathrm{dist}_G(z,z')\le D/2$ for all $z,z'\in Z$, and let $w\in V$. For every outcome:
--
--   (i) if $U_w\cap Z\ne\emptyset$, then $E_{touch}(w,Z)$ occurs; (ii) if $E_{cover}(w,Z)$ occurs, then $Z\subseteq X_w\subseteq U_w$; and (iii) conditioned on $\pi$ and on all radii other than $R_w$,
--   $$\Pr\big[E_{cover}(w,Z)\mid E_{touch}(w,Z)\big]\ge e^{-2}.$$
--   These two events are all the analysis of §4 needs to know about the approximate balls.
--
--   Differences from the source:
--
--   - encoding: a level 0 < ℓ < L with D = D_ℓ = 2^ℓ, L = ⌈log₂(nW)⌉ (§4.1) → hypotheses 0 < ℓ, ℓ < levels n W = Nat.clog 2 (n*W), D written 2^ℓ; reason: the section's fixed level made explicit
--   - reading: the output of Algorithm 2 ('compute X_i such that …', Blur's 'compute X_k such that …') → every valid execution: selectors X (function of π, R⃗) and Y (blur stage k of center w a function of π, R⃗ and r_{w,1..k}) satisfying (5), Algorithm 2 line 4 and Algorithm 3 line 5 (IsAlg2Exec); reason: a nondeterministic choice; quantifying over all choices is its meaning, and Lemmas 6.3/7.10 verify exactly these properties for the dynamic algorithms
--   - reading: for every outcome of the blur randomness → for every outcome in the support of the law: R_w ≥ 0 and r_{w,k} ∈ [0, α^{k−1}D/20] (IsOutcome); reason: outcomes outside the support have probability zero; on them (6) need not hold
--   - encoding: n vertices (α = 1/(2 log n) and log n need n ≥ 2) → hypothesis 2 ≤ n; reason: the only excluded case n = 1 makes log₂ n = 0 and α undefined
--   - encoding: undirected graph G = (V, E, w), integral weights in [1, W], connected (standing assumptions, p. 13) → G : WGraph (Fin n) with ℕ weights, HasWeightsIn W (or HasPosWeights), G.adj.Connected; dist in ℕ ∪ {∞}; reason: the standing assumptions of §3 made explicit; distances are integers
--   - generalization: polynomially bounded weights W ≤ n^{O(1)} (standing assumption) → any W (the statement has no constant depending on W); reason: the bound W ≤ n^{c_W} is a special case
--   - encoding: (iii) conditioned on π and all radii other than R_w → for every measurable event B of (π, (R_u)_{u≠w}): e^{−2}·P[E_touch ∩ B] ≤ P[E_cover ∩ B]; reason: the definition of conditional probability given σ(π, R_{−w})
--   - encoding: π uniform, R_w ∼ Exp(1/D) i.i.d. (rate 1/D, mean D) per vertex, blur radii r_{w,k} ∼ Unif[0, α^{k−1}σ], all independent → any probability space with a random outcome ζ satisfying IsAlg2Law (laws via Measure.map, iIndepFun, IndepFun); reason: a statement about every realization of the law is the statement about the law
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), pp. 14–15, Claim 4.2

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Static
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Claim 4.2** (pp. 14–15). Fix a connected graph on `n ≥ 2` vertices with integer weights in
`[1, W]`, a level `0 < ℓ < L = ⌈log₂(nW)⌉`, `D = 2^ℓ`, and a valid execution of Algorithm 2 with
parameter `D`. Let `Z` be nonempty with `dist_G(z, z') ≤ D/2` for all `z, z' ∈ Z`, and `w` a
vertex. For every outcome of the randomness: (i) if `U_w ∩ Z ≠ ∅` then `w` touches `Z`;
(ii) if `w` covers `Z` then `Z ⊆ X_w ⊆ U_w`. (iii) Conditioned on `π` and on all radii other than
`R_w`, `P[E_cover(w, Z) | E_touch(w, Z)] ≥ e^{−2}`: for every measurable event `B` of `π` and
`(R_u)_{u ≠ w}`, `P[E_cover ∩ B] ≥ e^{−2}·P[E_touch ∩ B]`. -/
theorem claim_4_2 (n W ℓ : ℕ) (G : WGraph (Fin n)) (hn : 2 ≤ n) (hconn : G.adj.Connected)
    (hW : G.HasWeightsIn W) (hℓ : 0 < ℓ) (hℓL : ℓ < levels n W)
    (X : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → Finset (Fin n))
    (Y : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → (ℕ → ℝ) → ℕ → Finset (Fin n))
    (hexec : IsAlg2Exec G (2 ^ ℓ) X Y) (Z : Finset (Fin n)) (hZ : Z.Nonempty)
    (hZdiam : ∀ z ∈ Z, ∀ z' ∈ Z, G.rdist z z' ≤ (2 : ℝ) ^ ℓ / 2) (w : Fin n) :
    (∀ ζ : Outcome n, IsOutcome ((2 : ℝ) ^ ℓ) ζ → (blurred Y (2 ^ ℓ) ζ w ∩ Z).Nonempty →
      Touches G (2 ^ ℓ) ζ.2.1 w Z) ∧
    (∀ ζ : Outcome n, IsOutcome ((2 : ℝ) ^ ℓ) ζ → Covers G (2 ^ ℓ) ζ.2.1 w Z →
      Z ⊆ X ζ.1 ζ.2.1 w ∧ X ζ.1 ζ.2.1 w ⊆ blurred Y (2 ^ ℓ) ζ w) ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (ζ : Ω → Outcome n),
      IsAlg2Law P n (2 ^ ℓ) ζ →
      ∀ B : Set (Equiv.Perm (Fin n) × ({u : Fin n // u ≠ w} → ℝ)), MeasurableSet B →
        ENNReal.ofReal (Real.exp (-2)) *
            P ({ω | Touches G (2 ^ ℓ) (ζ ω).2.1 w Z} ∩
              {ω | ((ζ ω).1, fun u : {u : Fin n // u ≠ w} => (ζ ω).2.1 u.1) ∈ B}) ≤
          P ({ω | Covers G (2 ^ ℓ) (ζ ω).2.1 w Z} ∩
              {ω | ((ζ ω).1, fun u : {u : Fin n // u ≠ w} => (ζ ω).2.1 u.1) ∈ B}) := by sorry

end PDynTreeEmbed.Main
