-- Prove2me | Theorems.Thm_RobustKZClust_Main_theorem_6_1
-- name    : RobustKZClust.Main.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:12:20.424906+00:00
-- url     : https://prove2.me/theorems/61303544-785e-4994-b6b6-b3e2fe50311e
-- title:
--   Theorem 6.1 — an adversarially robust dynamic-stream ε-oracle for (k, z)-clustering in Õ(k d^z ε^{−O(z)}) bits, Õ(k d ε^{−O(z)}) for z = 1, 2
-- statement:
--   Consider $(k,z)$-clustering in $\mathbb R^d$ on a dynamic stream of $m$ insertions and deletions of points of $[\Delta]^d$ chosen by an adaptive adversary. The adversary sees every function the algorithm reports. Let $\mu_t$ be the frequency vector after the $t$-th update.
--
--   **Theorem.** There are absolute constants $c_0,K_0$ such that for every integer $z\ge1$ and every $\delta_0\in(0,1)$ there are constants $C>0$ and $a\in\mathbb N$ with the following property. For all integers $k,d,\Delta,m\ge1$ and every $\varepsilon\in(0,1)$ there is a streaming algorithm with at most $K_0$ real registers and a deterministic query, such that:
--
--   1. every call halts on every tape: the initialization call, the update calls of every run of every valid adversary, and the query calls on valid lists after updates $1,\dots,m$;
--   2. at every step of each of these calls, on every run, the memory occupies at most
--   $$B=C\,k\,d^{z'}\,\varepsilon^{-c_0z}\,\bigl(\log_2(2+kdm\Delta/\varepsilon)\bigr)^{a}\ \text{bits},\qquad z'=\begin{cases}1,&z\in\{1,2\},\\ z,&z>2;\end{cases}$$
--   3. for every valid adaptive adversary,
--   $$\mathbb P_\omega\Bigl[\forall t\in[m],\ \forall C\subseteq\mathbb R^d,\ 1\le|C|\le k:\ (1-\varepsilon)\,\mathrm{cost}(\mu_t,C)\le\widehat{\mathrm{cost}}_t(C)\le(1+\varepsilon)\,\mathrm{cost}(\mu_t,C)\Bigr]\ge1-\delta_0,$$
--   where $C$ is given to the query as a duplicate-free list in any order.
--
--   So each reported $\widehat{\mathrm{cost}}_t$ is an $\varepsilon$-oracle for $\mu_t$ at all times simultaneously. This is the paper's main theorem; its $z\in\{1,2\}$ case is Theorem 1.3, and Theorem 1.1 follows from it.
--
--   **Formalization Note.** The failure event is bounded in outer measure under the product law of the per-call fair tapes. The bound $B$ is real-valued and compared with the bit count of the memory.
--
--   Differences from the source:
--   - reading: "adversarially robust streaming algorithm" in a model with exact real arithmetic and O(1) real registers (§2) → three programs of the mission's machine: integer memory charged in bits (addresses included) and persistent across calls, at most K₀ real registers reset at every call, fair coins, and a deterministic query; reason: the paper names no machine and §2 is the only description.
--   - reading: "with high constant probability" → for every δ₀ ∈ (0, 1), with C and a depending on z and δ₀; reason: the strongest reading of a constant success probability.
--   - reading: Õ(kd^z ε^{−O(z)}) for general z and Õ(kdε^{−O(z)}) for z = 1, 2 → C·k·d^{z'}·ε^{−c₀z}·(log₂(2 + kdm∆/ε))^a with c₀ absolute, z' = 1 for z ≤ 2 and z' = z otherwise; reason: Õ hides polylog(ε⁻¹kdm∆) (p. 2), and both printed clauses are kept as one bound.
--   - reading: the space bound → at every step of every call on every run (worst case), persistent memory and discrete workspace together; reason: §2 counts "stored bit strings and discrete workspace".
--   - reading: ε-oracle on all C ⊆ R^d with |C| ≤ k → all nonempty C with |C| ≤ k, given as a duplicate-free list in any order; reason: dist(x, ∅) is undefined, and the query must receive C in some order.
--   - reading: the adversary "observes all output" → it sees each reported function as a whole and chooses each update from the past updates and functions; deterministic adversaries; reason: strongest reading; randomized adversaries are mixtures of deterministic ones.
--   - encoding: the dataset P_t → the frequency vector µ_t of the updates (multiplicities allowed), valid adversaries delete only present points of [∆]^d; reason: the paper's µ_t ∈ N^X.
--   - encoding: "there is an algorithm" → the algorithm halts on every call it is asked to make; reason: an algorithm halts.
--   - reading: the parameters k, d, ∆, m → positive integers (1 ≤ k, d, ∆, m); reason: the source's k centers, R^d, the grid [∆]^d and t ∈ [m] presuppose them; each excluded value is degenerate (no valid query at k = 0, no valid update at ∆ = 0, nothing to report at m = 0, all costs 0 at d = 0).
-- source:
--   Guo, Jiang, Krauthgamer, Xie, Zhou, Adversarially Robust Streaming Algorithms for (k, z)-Clustering, STOC 2027 submission (manuscript sha256 7d9aadba…), p. 28, Theorem 6.1 (announced as Theorem 1.3, p. 2); model p. 13 §2; Õ convention p. 2

import Mathlib
import Definitions.Def_RobustKZClust_Main_Cost
import Definitions.Def_RobustKZClust_Main_Machine
import Definitions.Def_RobustKZClust_Main_Stream

namespace RobustKZClust.Main

/-- Theorem 6.1 (p. 28): an adversarially robust dynamic-stream ε-oracle for `(k, z)`-clustering
in `Õ(k d^z ε^{−O(z)})` bits, `Õ(k d ε^{−O(z)})` for `z = 1, 2`. -/
theorem theorem_6_1 :
    ∃ c₀ K₀ : ℕ, ∀ z : ℕ, 1 ≤ z → ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ k d Δ m : ℕ, 1 ≤ k → 1 ≤ d → 1 ≤ Δ → 1 ≤ m →
        ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ A : StreamAlg,
          RegsBelow A.init K₀ ∧ RegsBelow A.upd K₀ ∧ RegsBelow A.qry K₀ ∧
          Deterministic A.qry ∧
          -- every call halts
          (∀ ω : ℕ → Bool, ∃ s, Halted A.init (callRun A.init ω initInput zeroMem s)) ∧
          (∀ (adv : Adversary d), ValidAdversary Δ adv → ∀ (ω : ℕ → ℕ → Bool) (t : ℕ), t < m →
            ∃ s, Halted A.upd (callRun A.upd (ω (t + 1))
              (updInput (adv (runState A adv ω t).2)) (runState A adv ω t).1 s)) ∧
          (∀ (adv : Adversary d), ValidAdversary Δ adv → ∀ (ω : ℕ → ℕ → Bool) (t : ℕ),
            1 ≤ t → t ≤ m → ∀ L : List (Pt d), ValidQuery k L →
            ∃ s, Halted A.qry (callRun A.qry blankTape (queryInput L) (runState A adv ω t).1 s)) ∧
          -- worst-case bit space, at every step of every call
          (let B : ℝ := C * k * (d : ℝ) ^ (if z ≤ 2 then 1 else z) * ε ^ (-((c₀ * z : ℕ) : ℝ)) *
              Real.logb 2 (2 + (k : ℝ) * d * m * Δ / ε) ^ a
           (∀ (ω : ℕ → Bool) (s : ℕ), SpaceLE (callRun A.init ω initInput zeroMem s).mem B) ∧
           (∀ (adv : Adversary d), ValidAdversary Δ adv → ∀ (ω : ℕ → ℕ → Bool) (t : ℕ), t < m →
             ∀ s, SpaceLE (callRun A.upd (ω (t + 1))
               (updInput (adv (runState A adv ω t).2)) (runState A adv ω t).1 s).mem B) ∧
           (∀ (adv : Adversary d), ValidAdversary Δ adv → ∀ (ω : ℕ → ℕ → Bool) (t : ℕ),
             1 ≤ t → t ≤ m → ∀ L : List (Pt d), ValidQuery k L →
             ∀ s, SpaceLE (callRun A.qry blankTape (queryInput L)
               (runState A adv ω t).1 s).mem B)) ∧
          -- ε-oracle at all times, against every valid adaptive adversary
          (∀ (adv : Adversary d), ValidAdversary Δ adv →
            tapesMeasure {ω | ¬ ∀ t, 1 ≤ t → t ≤ m → ∀ L : List (Pt d), ValidQuery k L →
                (1 - ε) * cost z (freqAt A adv ω t) L.toFinset ≤ report A (runState A adv ω t).1 L ∧
                report A (runState A adv ω t).1 L ≤ (1 + ε) * cost z (freqAt A adv ω t) L.toFinset}
              ≤ ENNReal.ofReal δ₀) := by sorry

end RobustKZClust.Main
