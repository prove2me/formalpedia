-- Prove2me | Theorems.Thm_PulseSyncLowerBound_Pulse_lemma_16
-- name    : PulseSyncLowerBound.Pulse.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:04.942465+00:00
-- url     : https://prove2.me/theorems/ed8fb94e-d4d7-4b43-b80e-129c3edf9e6e
-- title:
--   Lemma 16 — offset advancement identity
-- statement:
--   Let $\sigma,f,n,q\in\mathbb N$ satisfy $q>\max\{2\sigma,1\}$, $f>0$, and $n>f+2$. Let $\mathcal A$ be a deterministic protocol with arbitrary finite nonempty local state spaces in the synchronous crash model. Assume that every execution with at most $f$ total crashes has a $\sigma$-lift from $T=\lfloor f/2\rfloor$. Set $X=R(T,2)$ and $Y=R(T+1,1)$ using all full initial configurations.
--
--   For every edge $\{y_i,y_j\}\in E(Y)$,
--
--   $$D(Sy_i,Sy_j)+\Delta(y_i)=D(Py_i,Py_j)+\Delta(y_j).$$
--
--   Here $\Delta(y)=(\operatorname{out}(Sy)-\operatorname{out}(Py))\bmod q$ is an integer in $[0,q)$. This is the complete cross-round consistency identity, retaining the orientation and the signed differences.
--
--   Differences from the source:
--   - encoding: processes numbered 1 through n with pairwise disjoint finite local state sets (operationally nonempty) → Fin n identities and arbitrary finite nonempty dependent local state types, with identity-tagged states and views; reason: zero-based relabelling and tagged disjoint union preserve every process, state, and execution; nonemptiness is the operational state convention used explicitly in the Lemma 12 proof
--   - encoding: outputs in Zq and lifts on non-faulty processes times Z → Fin q outputs and integer lifts on all identities at natural times, constrained only on non-faulty identities and t at least T; reason: Fin q is exactly the residue-label set; unconstrained identities and negative times extend arbitrarily, so all L1--L3 instances are preserved
--   - encoding: maps on the actual vertex set V(X) → maps on ambient tagged views constrained only when their singleton or edge is a face; reason: any map on actual vertices extends arbitrarily to the unused ambient views; no unreachable view is made a vertex
--   - generalization: the Section 6 protocol solves non-trivial counting, including N1 and N2 → assume only the universal lift property N1; reason: these statements concern local consistency, not indefinite progress; every source protocol satisfies N1, and the source proofs of Lemmas 13--17 do not use N2
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; Lemma 16; PDF p.23 / printed p.21; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f.

import Definitions.Def_PulseSyncLowerBound_Pulse_Offsets

namespace PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_16 {n q f σ : ℕ} (P : Protocol n (Fin q))
    (hq : max (2 * σ) 1 < q) (hf : 0 < f) (hn : f + 2 < n)
    (hN1 : LiftResilient P f σ (f / 2))
    (yi yj : TaggedView P (f / 2 + 1)) (he : IsEdge (Y P f) yi yj) :
    D P f σ (viewSuffix P (f / 2) yi) (viewSuffix P (f / 2) yj) + advancement P f yi =
      D P f σ (viewPrefix P (f / 2) yi) (viewPrefix P (f / 2) yj) + advancement P f yj := by sorry

end PulseSyncLowerBound.Pulse
