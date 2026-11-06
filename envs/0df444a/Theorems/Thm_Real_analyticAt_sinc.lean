-- Prove2me | Theorems.Thm_Real_analyticAt_sinc
-- name    : Real.analyticAt_sinc
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:39:30.426512+00:00
-- url     : https://prove2.me/theorems/b9c044a8-6d12-4f18-ae42-abe5eaec2263
-- title:
--   The Removable Sinc Function Is Real Analytic Everywhere
-- statement:
--   For every real x, the real function sinc is analytic at x, where sinc(x)=sin(x)/x for x≠0 and sinc(0)=1. In particular the assertion includes the removable point x=0.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Effectiveness.lean (file SHA-256 90d9fd8cedd8839d63110e1673758c66fd34eb170016cb9a2ad4c136d0777dd3):
--   Real.analyticAt_sinc at L331-L343 [UTF-8 16051:16769].

module
public import Definitions.Def_Monodromy_Effectiveness
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

theorem Real.analyticAt_sinc (x : ℝ) : AnalyticAt ℝ Real.sinc x := by sorry
