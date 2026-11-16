-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_Supplement_finite_coupling_accuracy
-- name    : SparseHamiltonianNorm.Simulation.Supplement.finite_coupling_accuracy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:31:07.424403+00:00
-- url     : https://prove2.me/theorems/c53dab5a-fd01-48c8-8db3-38b9bf0302ef
-- title:
--   Lemma 16 — Finite coupling accuracy on reachable histories
-- statement:
--   Let $V:\mathbb C^n\to E=\mathbb C^e$ be an isometry, let $\tau>0$, and let $G$ be even with $G\ge\max\{2,2\tau\}$. Set $\Delta=\tau/G$, $r=e^{-\Delta}$, and $L_R(\tau)=1+R^2/\min\{\tau,1\}$. Let $L\ge1$ make $M=G+2L$ a power of two, and let $R\ge1$.
--
--   There are absolute constants $c_0,C>0$ such that, if $\Delta L_R(\tau)\le c_0$ and $r^L\le1/2$, a complex linear isometry $E_\Delta:\mathcal F_{R-1}^{\rm sc}(\tau)\to\mathbb C^G$ exists, acting only on the history coordinate: one scalar map serves every fiber $E=\mathbb C^e$ and every isometry $V$. Its coordinatewise extension intertwines every matrix $T$ on $E$, and the pointwise lift of $T$ preserves the reachable space. The continuous scaled coupling $w_\tau=\operatorname{coupling}(1,1,\tau,V)$ maps the public space plus $\mathcal F_{R-2}^{\rm sc}(\tau)\otimes E$ into the public space plus $\mathcal F_{R-1}^{\rm sc}(\tau)\otimes E$. For every vector $(\xi,q)$ in the smaller domain,
--   $$\|\widetilde w^{(E)}\iota_{\rm grid}(\xi,E_\Delta^{(E)}q)-\iota_{\rm grid}((I\oplus E_\Delta^{(E)})w_\tau(\xi,q))\|\le C\bigl(\Delta L_R(\tau)+\Delta^2+e^{-\Delta L}\bigr)\sqrt{\|\xi\|^2+\|q\|^2}.$$
--   The finite operator is the full cyclic coupling, including all completion modes. The isometry is a comparison map on reachable histories, not a free circuit primitive. This is the continuous-to-finite estimate supporting the companion gate-realization theorem.
--
--   Differences from the source:
--   - generalization: the sparse-list isometry V of the paper → any isometry between finite complex Euclidean spaces; reason: the scalar-channel construction uses only V†V=I and includes every sparse-list embedding
--   - encoding: F^sc_(R−1) and F^sc_(R−2) in L²(0,τ) → spans with R and R−1 coefficients in the published L²([0,τ]) space; reason: endpoints are null and an empty span implements F^sc_(−1), including R=1
--   - encoding: the restricted operator norm and tensor intertwining in Eqs. (106)–(107) → the bound on every input with its orthogonal-sum norm, with explicit reachable-output and pointwise-lift membership; reason: this is the same restricted norm; the output membership is implicit in the displayed composition and proved on pp.30–32
--   - encoding: signed cyclic addresses −Lio through G+Lio−1 → standard residues Fin (G+2Lio), with p=M−1; reason: negative input addresses are mapped to their residues without changing the full unitary
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Lemma 16, p.29 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_Supplement_Cyclic

namespace SparseHamiltonianNorm.Simulation.Supplement
open QAlgorithms
/-- Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026),
Lemma 16, p.29, Eqs. (106)--(107). R counts coefficients in F^sc_(R-1).
The output-membership clause is established in Step 4, pp.30--32, not assumed.
The scalar isometry E∆ acts only on the history coordinate, so it is chosen
before the system space E = ℂ^e and the isometry V. -/
theorem finite_coupling_accuracy :
    ∃ c0 C : ℝ, 0 < c0 ∧ 0 < C ∧
    ∀ (τ : ℝ) (G L R : ℕ),
      0 < τ → Even G → 2 ≤ G → 2 * τ ≤ G → 1 ≤ L →
      (∃ b : ℕ, cyclicSize G L = 2 ^ b) → 1 ≤ R →
      mesh τ G * derivativeFactor R τ ≤ c0 → decay τ G ^ L ≤ 1 / 2 →
      ∃ E : scalarReachable τ R →ₗᵢ[ℂ] Vec G,
      ∀ (n e : ℕ) (V : Matrix (Fin e) (Fin n) ℂ), V.conjTranspose * V = 1 →
        (∀ (T : Matrix (Fin e) (Fin e) ℂ) (q : History e τ), InReachable R q →
          InReachable R (historyLift τ T q) ∧
          gridLift T (gridEncode E q) = gridEncode E (historyLift τ T q)) ∧
        (∀ (ξ : Vec n) (q : History e τ), InReachable (R - 1) q →
          InReachable R (coupling 1 1 τ V (ξ, q)).2 ∧
          ‖rectAction (finiteCoupling τ G L V)
                (logicalInclusion (L := L) V ξ (gridEncode E q)) -
              logicalInclusion (L := L) V (coupling 1 1 τ V (ξ, q)).1
                (gridEncode E (coupling 1 1 τ V (ξ, q)).2)‖ ≤
            C * (mesh τ G * derivativeFactor R τ + (mesh τ G) ^ 2 +
              Real.exp (-mesh τ G * L)) * Real.sqrt (‖ξ‖ ^ 2 + ‖q‖ ^ 2)) := by sorry
end SparseHamiltonianNorm.Simulation.Supplement
