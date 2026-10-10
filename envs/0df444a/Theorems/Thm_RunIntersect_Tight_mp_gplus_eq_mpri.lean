-- Prove2me | Theorems.Thm_RunIntersect_Tight_mp_gplus_eq_mpri
-- name    : RunIntersect.Tight.mp_gplus_eq_mpri
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:03.380922+00:00
-- url     : https://prove2.me/theorems/a1bb7def-7875-4f21-82d2-69945bcb95ec
-- title:
--   §5.3.1, p. 1035 — inductive step: MP_{G⁺} = MP^RI_{G⁺}
-- statement:
--   Let $G=(V,E)$ be a kite-free β-acyclic hypergraph with no isolated node and $\kappa\ge 2$ maximal edges; let $\mathcal O$, $\tilde e$, $\bar p=N(\tilde e)$ and $G^+$ be as in §5.3.1 (the last maximal edge of a running intersection ordering, its set (3), and $G$ with $\bar p$ added when $|\bar p|\ge 2$). Assume the induction hypothesis of the proof of Theorem 3: every kite-free β-acyclic hypergraph $H$ (on the same ground type) without isolated nodes and with fewer than $\kappa$ maximal edges satisfies $\mathrm{MP}_H=\mathrm{MP}^{\mathrm{RI}}_H$. Then
--   $$\mathrm{MP}_{G^+}=\mathrm{MP}^{\mathrm{RI}}_{G^+}.$$
--
--   In the paper this follows from $\mathrm{MP}_{G_\alpha}=\mathrm{MP}^{\mathrm{RI}}_{G_\alpha}$, $\mathrm{MP}_{G_\omega}=\mathrm{MP}^{\mathrm{RI}}_{G_\omega}$ and the decomposability of $\mathcal S_{G^+}$; it is the lifted half of the inductive step.
--
--   **Formalization Note** This item carries the induction hypothesis as an explicit binder `ih`: it is the inductive step as the paper states it, not a lemma with fewer hypotheses. The hypothesis that $G$ has no isolated node is a disclosed addition, necessary for the same reason as in Theorem 3: an isolated node $c$ of $G$ is an isolated node of $G^+$, and the point with $z_c=-1$ (all else $0$) lies in $\mathrm{MP}^{\mathrm{RI}}$ but not in $\mathrm{MP}$ (example $V=\{a,b,c\}$, $E=\{\{a,b\}\}$).
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1035, §5.3.1 (proof of Theorem 3), end of second paragraph

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

namespace RunIntersect.Tight

theorem mp_gplus_eq_mpri {α : Type*} [Fintype α] [DecidableEq α]
    (G : Hypergraph α) (hkite : IsKiteFree G) (hβ : IsBetaAcyclic G)
    (O : List (Finset α)) (hOnd : O.Nodup) (hO : O.toFinset = maxEdges G) (hOri : IsRIOrder O)
    (hκ : 2 ≤ O.length)
    (hiso : NoIsolated G)
    (ih : ∀ H : Hypergraph α, IsKiteFree H → IsBetaAcyclic H → NoIsolated H →
      (maxEdges H).card < O.length → MP H = MPRI H) :
    MP (GplusLast G O) = MPRI (GplusLast G O) := by sorry

end RunIntersect.Tight
