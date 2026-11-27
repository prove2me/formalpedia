-- Prove2me | Theorems.Thm_SingleExpBisect_Main_charged_child_convolution
-- name    : SingleExpBisect.Main.charged_child_convolution
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:39:33.81807+00:00
-- url     : https://prove2.me/theorems/634742c6-1628-5b6f-9105-ee52c5af20af
-- title:
--   Section 3 — charged single-exponential sparse child convolution, with bounded intermediate coefficients
-- statement:
--   The evaluator scans the complete child boundary signature, shifts signed Laurent degrees, and adds equal products after each child. The proof relates the table to the registered Section 3.1 recurrence, counts its projections, coefficient operations and table probes, and bounds all intermediate coefficients for every prefix. The operation count is at most stepBound 128 k n under the registered Section 3 decomposition hypotheses. This bound counts the stated table operations on supplied child records. Parsing the TM2 input, constructing those records, and bit-level arithmetic are separate parts of the original machine problem.
-- source:
--   Kumabe, Single-Exponential Algorithm for Minimum Bisection, STOC project #803, Section 3, Lemmas 3.1 and 3.4–3.6.

import Definitions.Def_SingleExpBisect_Main_ChargedChildConvolution

open SingleExpBisect.Convolution SingleExpBisect.Main MinBisectFPT SingleExpBisect.Sparse

theorem SingleExpBisect.Main.charged_child_convolution {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n)
    (k : ℕ) (ht : IsSec3Decomp G T k) (t : Fin T.N) (R : Finset (Fin n))
    (hr : R⊆T.bag t) (Lc : Fin T.N → List (Entry n)) (rep : ∀ s,T.parent s=some t →
     IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) (q : Degrees) :
    let base : ℤ := ((cutSize (bagGraph G T t) R + etaNode G T t (R∩T.adhesion t):ℕ):ℤ)
    let cs := records G T t R Lc
    let M := (n+1)*(k+1)
    let D := (cs.length*n+1)*(cs.length*k+1)
    (fast k base cs q).1=(toL (Qpoly G (T.cone t) (T.bag t) k R)).coeff
      (Finsupp.single .x q.x + Finsupp.single .x' q.aux + Finsupp.single .w q.w) ∧
    (fast k base cs q).2 ≤ stepBound 128 k n ∧
    (fast k base cs q).2 ≤ 3+cs.length*2+(cs.map (fun p => p.2.2.length)).sum*(n+3)
        +cs.length*(D+1+D*M*(D+4))+D ∧
    ∀ pre post,cs=pre++post →
      ∀ z∈(layers degreesAdd [(wDegree base,1)] (pre.map (fun p=> (shifted p).2))).1,
        ∃ j : ℕ,z.2=(j:ℚ) ∧ j ≤ (M*2^n)^pre.length := by sorry
