-- Prove2me | Theorems.Thm_ShmoysOnline_ReleaseDates_theorem_2_1
-- name    : ShmoysOnline.ReleaseDates.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:56:50.744221+00:00
-- url     : https://prove2.me/theorems/98507685-8744-4f45-87b9-a6fb5fb1104f
-- title:
--   Theorem 2.1 — removing advance knowledge of release dates
-- statement:
--   Consider a family of static resource configurations $v$, each with an environment $E_v$ and an honest processing/completion port $P_v$ carrying its admission-information rule. For each configuration let $\rho_v\ge1$. Let $\mathcal A$ be one uniform polynomial-time scheduler, with a single code list independent of $v$, that, on every finite nonempty zero-release batch, produces a feasible schedule of length at most $\rho_v$ times the zero-release off-line optimum. Write its computation bound as $c(N+1)^d$, with $c>0$ and $d\in\mathbb N$ independent of both the batch and the configuration.
--
--   The §2 batching controller gives one causal polynomial-time scheduler for unknown release dates, with the same resources, admission information, processing observations and preemption/restart rules. For every configuration $v$ and every finite valid released instance $I$, its execution and event stream exist, its batches are disjoint and cover all jobs, it makes at most $n=|J|$ nonempty invocations, and its assembled schedule $S$ is feasible. Moreover,
--   $$C_{\max}(S)\le 2\rho_v\,C_{\max}^{*}(I).$$
--   There is no additive slack. More explicitly, this inequality holds against every feasible off-line schedule of the original released instance. Under the stated cost convention the computational conclusion is
--   $$\operatorname{cost}(I)\le n c\bigl(N(I)+1\bigr)^d+10\bigl(N(I)+1\bigr)^2.$$
--   The controller, base code and polynomial constants are fixed before the configuration and $I$ are chosen; the total number of future jobs, their data and release dates, and the final-arrival time are not inputs to the policy. Empty input produces makespan zero.
--
--   The theorem transfers zero-release makespan guarantees to the analogous environment with unknown arrivals, including the case in which processing sizes remain hidden until completion.
--
--   **Formalization Note** This is the full transformation statement, not a supplied-trace inequality. The off-line optimum is represented by universal comparison with feasible schedules, equivalent to its infimum because feasible makespans form a nonempty set bounded below by zero. Time is real. Polynomial computation is stated in the explicit finite-cell real-RAM/processing-port model. The constant $2\rho$ is exactly the paper's; the coefficient 10 only makes the wrapper's polynomial bookkeeping explicit and is not a makespan constant.
-- source:
--   Shmoys, Wein and Williamson, Scheduling Parallel Machines On-Line, SIAM J. Comput. 24(6) (1995), DOI https://doi.org/10.1137/S0097539793248317; Theorem 2.1 p. 1316 (PDF 4), proof pp. 1316–1317 (PDF 4–5).

import Definitions.Def_ShmoysOnline_ReleaseDates_Batching

set_option autoImplicit false
open scoped NNReal
noncomputable section

namespace ShmoysOnline.ReleaseDates

/-- Theorem 2.1: a single batching controller preserves the base processing port,
uses uniform polynomial computation across configurations, and achieves exactly
2ρ against every feasible released comparator. -/
theorem theorem_2_1 {V : Type} {D : V → Type} [∀ v, Inhabited (D v)]
    (E : (v : V) → Environment (D v)) (P : (v : V) → Protocol (D v))
    (A : UniformAlgorithm V D) (hP : ∀ v, HonestProcessing (E v) (P v))
    (ρ : V → ℝ≥0) (hρ : ∀ v, 1 ≤ ρ v) (c d : ℕ)
    (hA : ∀ v, Eligible (E v) (P v) (specialize A v) (ρ v) c d) :
    ControllerCausal ∧
    ∀ (v : V) (I : Instance (D v)), Valid (E v) I →
      ∃ (bs : List Batch) (es : List Packet),
        BatchExecution (P v) (specialize A v) I I.jobs 0 bs ∧
        EventsFor (P v) (specialize A v) I bs es ∧
        (controllerRun es).2.1 = bs.map (fun b => (b.start, b.jobs)) ∧
        bs.length ≤ I.jobs.card ∧
        (bs.map (fun b => b.jobs.toFinset)).Pairwise Disjoint ∧
        (bs.flatMap Batch.jobs).toFinset = I.jobs ∧
        computationCost (P v) (specialize A v) I bs es ≤
          I.jobs.card * c * (releasedInputSize (P v) I + 1) ^ d +
            10 * (releasedInputSize (P v) I + 1) ^ 2 ∧
        Approx (E v) I (2 * ρ v) (assembled (P v) (specialize A v) I bs) := by sorry

end ShmoysOnline.ReleaseDates

/- BEGIN IMPORTED LEAN FOR BLIND AUDIT

import Mathlib

set_option autoImplicit false
open scoped NNReal
noncomputable section

namespace ShmoysOnline.ReleaseDates

/-- A finite piece of a job's local execution; resources may be a whole submesh.
The tag distinguishes operations or attempts within a job. -/
structure Slice where
  lo : ℝ≥0
  hi : ℝ≥0
  resources : Finset ℕ
  tag : ℕ
  deriving DecidableEq

abbrev Profile := List Slice

def span (p : Profile) : ℝ≥0 := (p.map Slice.hi).foldr max 0

def WellFormed (resources : Finset ℕ) (p : Profile) : Prop :=
  p ≠ [] ∧ ∀ s ∈ p, s.lo < s.hi ∧ s.resources.Nonempty ∧ s.resources ⊆ resources

/-- Static, job-local constraints. There are no constraints between different jobs
except exclusive use of the fixed resources. Operations within a shop job, mesh
requirements and restart/preemption rules belong to `legal`. -/
structure Environment (D : Type) where
  resources : Finset ℕ
  legal : D → Profile → Prop
  /-- Completed internal operations observable from actual processing. -/
  progress : D → Profile → Finset ℕ

def Admissible {D : Type} (E : Environment D) (d : D) : Prop :=
  ∃ p, WellFormed E.resources p ∧ E.legal d p

structure Instance (D : Type) where
  jobs : Finset ℕ
  data : ℕ → D
  release : ℕ → ℝ≥0

def Valid {D : Type} (E : Environment D) (I : Instance D) : Prop :=
  ∀ j ∈ I.jobs, Admissible E (I.data j)

structure Placement where
  start : ℝ≥0
  profile : Profile
  deriving Inhabited

abbrev Schedule := ℕ → Placement

def completion (s : Schedule) (j : ℕ) : ℝ≥0 := (s j).start + span (s j).profile

noncomputable def makespan (J : Finset ℕ) (s : Schedule) : ℝ≥0 :=
  J.sup (completion s)

def Feasible {D : Type} (E : Environment D) (I : Instance D) (s : Schedule) : Prop :=
  (∀ j ∈ I.jobs, I.release j ≤ (s j).start ∧
    WellFormed E.resources (s j).profile ∧ E.legal (I.data j) (s j).profile) ∧
  (∀ j ∈ I.jobs, ∀ k ∈ I.jobs, j ≠ k →
    ∀ a ∈ (s j).profile, ∀ b ∈ (s k).profile,
      ¬ Disjoint a.resources b.resources →
      (s j).start + a.hi ≤ (s k).start + b.lo ∨
      (s k).start + b.hi ≤ (s j).start + a.lo)

def zeroInstance {D : Type} (I : Instance D) (J : Finset ℕ) : Instance D :=
  ⟨J, I.data, fun _ => 0⟩

def restrictInstance {D : Type} (I : Instance D) (J : Finset ℕ) : Instance D :=
  { I with jobs := I.jobs ∩ J }

def translate (t : ℝ≥0) (s : Schedule) : Schedule :=
  fun j => { s j with start := t + (s j).start }

/-- Used only when every selected placement starts at or after `t`. -/
def untranslate (t : ℝ≥0) (s : Schedule) : Schedule :=
  fun j => { s j with start := (s j).start - t }

noncomputable def join (J : Finset ℕ) (s u : Schedule) : Schedule :=
  fun j => if j ∈ J then s j else u j

/-- Comparator formulation of the pure multiplicative guarantee. No arbitrary OPT
parameter, no infimum of an empty set, and no additive constant. -/
def Approx {D : Type} (E : Environment D) (I : Instance D)
    (ρ : ℝ≥0) (s : Schedule) : Prop :=
  Feasible E I s ∧ ∀ u, Feasible E I u → makespan I.jobs s ≤ ρ * makespan I.jobs u

inductive Mode where
  | nonpreemptive | restart | preemptive
  deriving DecidableEq

structure ParallelJob (m : ℕ) where
  size : ℝ≥0
  speed : Fin m → ℝ≥0

/-- No job runs on two machines at once, including canceled attempts. -/
def SerialProfile (p : Profile) : Prop :=
  p.Pairwise (fun a b => a.hi ≤ b.lo)

noncomputable def work {m : ℕ} (d : ParallelJob m) (p : Profile) : ℝ≥0 :=
  (p.map fun a => (a.hi - a.lo) * ∑ i : Fin m,
    if a.resources = {i.val} then d.speed i else 0).sum

/-- An uninterrupted successful final attempt. Earlier restart attempts are charged
resource time but contribute no surviving work. -/
def successfulAttempt {m : ℕ} (d : ParallelJob m) (a : Slice) : Prop :=
  ∃ i : Fin m, a.resources = {i.val} ∧
    (a.hi - a.lo) * d.speed i = d.size

noncomputable def parallel (m : ℕ) (mode : Mode) : Environment (ParallelJob m) where
  resources := Finset.range m
  progress _ _ := ∅
  legal d p := 0 < d.size ∧ (∀ i, 0 < d.speed i) ∧ SerialProfile p ∧
    (∀ a ∈ p, ∃ i : Fin m, a.resources = {i.val}) ∧
    match mode with
    | .nonpreemptive => ∃ a, p = [a] ∧ successfulAttempt d a
    | .restart => ∃ canceled a, p = canceled ++ [a] ∧ successfulAttempt d a ∧
        ∀ b ∈ canceled, ∃ i : Fin m, b.resources = {i.val} ∧
          (b.hi - b.lo) * d.speed i < d.size
    | .preemptive => work d p = d.size

def identicalJob {m : ℕ} (p : ℝ≥0) : ParallelJob m := ⟨p, fun _ => 1⟩
def uniformJob {m : ℕ} (p : ℝ≥0) (speed : Fin m → ℝ≥0) : ParallelJob m := ⟨p, speed⟩

structure ShopOperation where
  machine : ℕ
  duration : ℝ≥0

structure ShopJob where
  operations : List ShopOperation
  precedes : ℕ → ℕ → Prop

def finishedOperations (d : ShopJob) (p : Profile) : Finset ℕ := by
  classical
  exact ((p.filter fun a => ∃ o, d.operations[a.tag]? = some o ∧
    a.resources = {o.machine} ∧ a.hi - a.lo = o.duration).map Slice.tag).toFinset

/-- Open shops use no precedence pairs; flow/job shops encode their fixed
within-job operation order. The same finite resource interface handles all three. -/
def shop (m : ℕ) : Environment ShopJob where
  resources := Finset.range m
  progress := finishedOperations
  legal d p := d.operations ≠ [] ∧
    (∀ o ∈ d.operations, o.machine < m ∧ 0 < o.duration) ∧
    SerialProfile p ∧ p.length = d.operations.length ∧
    (∀ k < d.operations.length, ∃ a ∈ p, a.tag = k ∧
      ∃ o, d.operations[k]? = some o ∧ a.resources = {o.machine} ∧
        a.hi - a.lo = o.duration) ∧
    (∀ a ∈ p, ∀ b ∈ p, d.precedes a.tag b.tag → a.hi ≤ b.lo)

structure MeshJob where
  size : ℝ≥0
  allowed : Finset (Finset ℕ)

/-- Permitted submeshes (or other static processor subsets) are part of job data. -/
def mesh (resources : Finset ℕ) : Environment MeshJob where
  resources := resources
  progress _ _ := ∅
  legal d p := 0 < d.size ∧ ∃ a, p = [a] ∧
    a.resources ∈ d.allowed ∧ a.hi - a.lo = d.size

end ShmoysOnline.ReleaseDates

import Definitions.Def_ShmoysOnline_ReleaseDates_Model

set_option autoImplicit false
open scoped NNReal
noncomputable section

namespace ShmoysOnline.ReleaseDates

abbrev BatchData (D : Type) := List (ℕ × D)

noncomputable def batchData {D : Type} (I : Instance D) (J : Finset ℕ) : BatchData D :=
  (J.sort (· ≤ ·)).map (fun j => (j, I.data j))

def batchInstance {D : Type} [Inhabited D] (B : BatchData D) : Instance D :=
  ⟨(B.map Prod.fst).toFinset,
    fun j => ((B.find? (fun x => x.1 == j)).map Prod.snd).getD default,
    fun _ => 0⟩

def ValidBatch {D : Type} (E : Environment D) (B : BatchData D) : Prop :=
  (B.map Prod.fst).Nodup ∧ ∀ x ∈ B, Admissible E x.2

/-- The physical executor records slices; the algorithm sees only `answer` and the
elapsed local clock. Slices are absolute in the invocation's local time. -/
structure Observation where
  elapsed : ℝ≥0
  answer : List ℝ
  pieces : List (ℕ × Slice)

structure Interaction where
  query : List ℝ
  observation : Observation

/-- An information/physics port, fixed for the base algorithm and wrapper alike.
`observe` is a causal interaction oracle: its arguments are only the admitted batch,
previous interactions and the present request. It is not given any future jobs or
release dates. The oracle implements the chosen environment's processing and
completion feedback; its observations are not unit-cost computational solutions. -/
structure Protocol (D : Type) where
  staticInput : List ℝ
  encode : D → List ℝ
  decode : List ℝ → Option D
  decode_encode : ∀ d, decode (encode d) = some d
  admission : D → List ℝ
  admission_length : ∀ d, (admission d).length ≤ (encode d).length
  observe : BatchData D → List Interaction → List ℝ → Option Observation

/-- Standard admission choices for the parallel-machine instances. Relative
machine speeds are visible in either case; only the size is hidden. -/
inductive SizeInformation where
  | known | hidden
  deriving DecidableEq

def parallelEncoding {m : ℕ} (d : ParallelJob m) : List ℝ :=
  (d.size : ℝ) :: List.ofFn (fun i => (d.speed i : ℝ))

def parallelAdmission {m : ℕ} (info : SizeInformation) (d : ParallelJob m) : List ℝ :=
  match info with
  | .known => parallelEncoding d
  | .hidden => List.ofFn (fun i => (d.speed i : ℝ))

/-- Finite-cell real-RAM input. Full encodings are used to measure cost only;
initial registers contain public encodings. -/
def inputSize {D : Type} (P : Protocol D) (B : BatchData D) : ℕ :=
  1 + P.staticInput.length + (B.map (fun x => 2 + (P.encode x.2).length)).sum

def publicInput {D : Type} (P : Protocol D) (B : BatchData D) : List ℝ :=
  P.staticInput ++ [(B.length : ℝ)] ++
    B.flatMap (fun x => [(x.1 : ℝ), ((P.admission x.2).length : ℝ)] ++ P.admission x.2)

inductive Instruction where
  | constant (dst : ℕ) (value : ℝ)
  | copy (dst src : ℕ)
  | add (dst left right : ℕ)
  | sub (dst left right : ℕ)
  | mul (dst left right : ℕ)
  | div (dst left right : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | branchLE (left right yes no : ℕ)
  | jump (target : ℕ)
  | clock (dst : ℕ)
  | answer (dst index : ℕ)
  | query (lengthRegister : ℕ)
  | halt

structure MachineState where
  pc : ℕ
  reg : ℕ → ℝ
  now : ℝ≥0
  history : List Interaction
  cost : ℕ

noncomputable def initialState {D : Type} (P : Protocol D) (B : BatchData D) : MachineState :=
  ⟨0, fun i => (publicInput P B)[i]?.getD 0, 0, [], (publicInput P B).length⟩

def halted (code : List Instruction) (s : MachineState) : Prop :=
  code[s.pc]? = some .halt

noncomputable def machineStep {D : Type} (P : Protocol D) (B : BatchData D)
    (code : List Instruction) (s : MachineState) : MachineState := by
  classical
  let next := { s with pc := s.pc + 1, cost := s.cost + 1 }
  let put := fun (i : ℕ) (x : ℝ) => { next with reg := Function.update s.reg i x }
  exact match code[s.pc]? with
  | none => next
  | some (.halt) => s
  | some (.constant i x) => put i x
  | some (.copy i j) => put i (s.reg j)
  | some (.add i j k) => put i (s.reg j + s.reg k)
  | some (.sub i j k) => put i (s.reg j - s.reg k)
  | some (.mul i j k) => put i (s.reg j * s.reg k)
  | some (.div i j k) => put i (s.reg j / s.reg k)
  | some (.load i j) => put i (s.reg ⌊s.reg j⌋₊)
  | some (.store i j) => { next with reg := Function.update s.reg ⌊s.reg i⌋₊ (s.reg j) }
  | some (.branchLE i j yes no) => { next with pc := if s.reg i ≤ s.reg j then yes else no }
  | some (.jump target) => { next with pc := target }
  | some (.clock i) => put i s.now
  | some (.answer i j) =>
      put i (((((s.history.getLast?).map (fun x => x.observation.answer)).getD [])[⌊s.reg j⌋₊]?).getD 0)
  | some (.query l) =>
      let q := (List.range ⌊s.reg l⌋₊).map s.reg
      match P.observe B s.history q with
      | none => s
      | some o =>
        { next with
          now := s.now + o.elapsed
          history := s.history ++ [⟨q, o⟩]
          cost := s.cost + 1 + q.length + o.answer.length + o.pieces.length }

noncomputable def machineRun {D : Type} (P : Protocol D) (B : BatchData D)
    (code : List Instruction) : ℕ → MachineState
  | 0 => initialState P B
  | k + 1 => machineStep P B code (machineRun P B code k)

/-- Consecutive pieces with the same resource allocation and attempt/operation tag
are one uninterrupted interval, even if another job generated a completion event. -/
def coalesce : Profile → Profile
  | [] => []
  | a :: rest =>
      match coalesce rest with
      | [] => [a]
      | b :: tail =>
          if a.hi = b.lo ∧ a.resources = b.resources ∧ a.tag = b.tag then
            { a with hi := b.hi } :: tail
          else a :: b :: tail

/-- Actual execution recorded by the physical port. -/
def recordedSchedule (h : List Interaction) : Schedule := fun j =>
  ⟨0, coalesce ((h.flatMap (fun x => x.observation.pieces)).filterMap
    (fun x => if x.1 = j then some x.2 else none))⟩

/-- Each request is a positive timeout (negative means wait until a completion)
followed by triples (job id, operation or
attempt tag, resource bit mask). The allocation stays fixed until feedback. -/
def allocations (resources : Finset ℕ) : List ℝ → List (ℕ × ℕ × Finset ℕ)
  | j :: tag :: mask :: rest =>
      (⌊j⌋₊, ⌊tag⌋₊, resources.filter (fun i => (⌊mask⌋₊).testBit i)) ::
        allocations resources rest
  | _ => []

def requestTime (q : List ℝ) : ℝ≥0 := ((q[0]?.getD (0 : ℝ))).toNNReal

def plannedPieces (resources : Finset ℕ) (now dt : ℝ≥0)
    (q : List ℝ) : List (ℕ × Slice) :=
  (allocations resources (q.drop 1)).map (fun a =>
    (a.1, ⟨now, now + dt, a.2.2, a.2.1⟩))

def completed {D : Type} (E : Environment D) (B : BatchData D)
    (h : List Interaction) : Finset ℕ := by
  classical
  exact (B.filter (fun x =>
    WellFormed E.resources (recordedSchedule h x.1).profile ∧
      E.legal x.2 (recordedSchedule h x.1).profile)).map Prod.fst |>.toFinset

/-- Signal 0 denotes completion of the whole job; signal k+1 denotes completion
of internal operation k. Only progress of executed profiles is observable. -/
def feedback {D : Type} (E : Environment D) (B : BatchData D)
    (h : List Interaction) : Finset (ℕ × ℕ) :=
  (completed E B h).image (fun j => (j, 0)) ∪
    (B.flatMap (fun x => ((E.progress x.2 (recordedSchedule h x.1).profile).toList.map
      (fun k => (x.1, k + 1))))).toFinset

def legalRequest {D : Type} (E : Environment D) (B : BatchData D)
    (h : List Interaction) (q : List ℝ) : Prop :=
  (((q[0]?.getD (0 : ℝ))) < 0 ∨ 0 < requestTime q) ∧ (q.length - 1) % 3 = 0 ∧
  let a := allocations E.resources (q.drop 1)
  (a.map Prod.fst).Nodup ∧
  (∀ x ∈ a, x.1 ∈ (B.map Prod.fst).toFinset ∧ x.1 ∉ completed E B h ∧
    x.2.2.Nonempty) ∧ a.Pairwise (fun x y => Disjoint x.2.2 y.2.2)

def elapsedTime (h : List Interaction) : ℝ≥0 :=
  (h.map (fun x => x.observation.elapsed)).sum

def hypothetical {D : Type} (E : Environment D) (h : List Interaction)
    (q : List ℝ) (dt : ℝ≥0) : List Interaction :=
  h ++ [⟨q, ⟨dt, [], plannedPieces E.resources (elapsedTime h) dt q⟩⟩]

/-- A processing port can only execute the requested allocation until the timeout
or first completion signal, and report exactly the newly completed job/operation identities. This
prevents an oracle from doing hidden scheduling or returning unearned information. -/
def HonestProcessing {D : Type} (E : Environment D) (P : Protocol D) : Prop :=
  ∀ B h q, ValidBatch E B → legalRequest E B h q →
    match P.observe B h q with
    | none => ((q[0]?.getD (0 : ℝ))) < 0 ∧
        ∀ dt : ℝ≥0, 0 < dt →
          feedback E B (hypothetical E h q dt) \ feedback E B h = ∅
    | some o =>
      let new := feedback E B (hypothetical E h q o.elapsed) \ feedback E B h
      0 < o.elapsed ∧
      (0 ≤ (q[0]?.getD (0 : ℝ)) → o.elapsed ≤ requestTime q) ∧
      o.pieces = plannedPieces E.resources (elapsedTime h) o.elapsed q ∧
      o.answer = new.toList.flatMap (fun x => [(x.1 : ℝ), (x.2 : ℝ)]) ∧
      (((q[0]?.getD (0 : ℝ)) < 0 ∨ o.elapsed < requestTime q) → new.Nonempty) ∧
      ∀ dt : ℝ≥0, 0 < dt → dt < o.elapsed →
        feedback E B (hypothetical E h q dt) \ feedback E B h = ∅

structure BaseAlgorithm (D : Type) where
  code : List Instruction
  /-- A denotational execution horizon, never supplied to the running program. -/
  steps : BatchData D → ℕ

/-- Uniformity across visible resource configurations: code, and later its
polynomial constants, do not depend on a configuration such as the machine count.
Only the denotational termination witness is indexed by the configuration. -/
structure UniformAlgorithm (V : Type) (D : V → Type) where
  code : List Instruction
  steps : (v : V) → BatchData (D v) → ℕ

def specialize {V : Type} {D : V → Type} (A : UniformAlgorithm V D)
    (v : V) : BaseAlgorithm (D v) := ⟨A.code, A.steps v⟩

noncomputable def baseState {D : Type} (P : Protocol D) (A : BaseAlgorithm D)
    (B : BatchData D) : MachineState := machineRun P B A.code (A.steps B)

noncomputable def baseSchedule {D : Type} (P : Protocol D) (A : BaseAlgorithm D)
    (B : BatchData D) : Schedule := recordedSchedule (baseState P A B).history

/-- A real polynomial bound on actual interpreted computation. The same program,
constant and degree work for every finite admitted batch. Physical time is excluded. -/
def Eligible {D : Type} [Inhabited D] (E : Environment D) (P : Protocol D)
    (A : BaseAlgorithm D) (ρ : ℝ≥0) (c d : ℕ) : Prop :=
  0 < c ∧ ∀ B, ValidBatch E B → B ≠ [] →
    (∀ k < A.steps B, ∀ l,
      A.code[(machineRun P B A.code k).pc]? = some (.query l) →
      legalRequest E B (machineRun P B A.code k).history
        ((List.range ⌊(machineRun P B A.code k).reg l⌋₊).map
          (machineRun P B A.code k).reg)) ∧
    halted A.code (baseState P A B) ∧
    (baseState P A B).cost ≤ c * (inputSize P B + 1) ^ d ∧
    (baseState P A B).now = makespan (batchInstance B).jobs (baseSchedule P A B) ∧
    Approx E (batchInstance B) ρ (baseSchedule P A B)

end ShmoysOnline.ReleaseDates

import Definitions.Def_ShmoysOnline_ReleaseDates_Algorithm

set_option autoImplicit false
open scoped NNReal
noncomputable section

namespace ShmoysOnline.ReleaseDates

structure Packet where
  time : ℝ≥0
  arrivals : List ℕ
  finished : Bool
  deriving DecidableEq

structure ControllerState where
  waiting : List ℕ
  busy : Bool
  deriving DecidableEq

/-- One event, combining all arrivals at the event time with a possible completion.
The completion is processed before testing the enlarged waiting queue. -/
def controllerStep (s : ControllerState) (e : Packet) : ControllerState × List ℕ :=
  let waiting := s.waiting ++ e.arrivals.mergeSort (fun a b => decide (a ≤ b))
  if s.busy && !e.finished then (⟨waiting, true⟩, [])
  else if waiting.isEmpty then (⟨[], false⟩, [])
  else (⟨[], true⟩, waiting)

/-- List-cell copying, queue scanning, and constant event dispatch cost. -/
def controllerStepCost (s : ControllerState) (e : Packet) : ℕ :=
  3 + s.waiting.length + e.arrivals.length + e.arrivals.length ^ 2 +
    (controllerStep s e).2.length

def controllerRun (es : List Packet) : ControllerState × List (ℝ≥0 × List ℕ) × ℕ :=
  es.foldl (fun r e =>
    let z := controllerStep r.1 e
    (z.1, r.2.1 ++ (if z.2.isEmpty then [] else [(e.time, z.2)]),
      r.2.2 + controllerStepCost r.1 e)) (⟨[], false⟩, [], 0)

/-- One action per event, including empty actions. This is a trace of the full
execution, so prefix causality compares full runs on different continuations. -/
def controllerActionsFrom (s : ControllerState) : List Packet → List (ℝ≥0 × List ℕ)
  | [] => []
  | e :: es =>
      let z := controllerStep s e
      (e.time, z.2) :: controllerActionsFrom z.1 es

def ControllerCausal : Prop :=
  ∀ (h k : List Packet) (n : ℕ), h.take n = k.take n →
    (controllerActionsFrom ⟨[], false⟩ h).take n =
      (controllerActionsFrom ⟨[], false⟩ k).take n

structure Batch where
  start : ℝ≥0
  jobs : List ℕ
  deriving DecidableEq

noncomputable def batchSchedule {D : Type} (P : Protocol D) (A : BaseAlgorithm D)
    (I : Instance D) (b : Batch) : Schedule :=
  baseSchedule P A (b.jobs.map (fun j => (j, I.data j)))

noncomputable def batchFinish {D : Type} (P : Protocol D) (A : BaseAlgorithm D)
    (I : Instance D) (b : Batch) : ℝ≥0 :=
  b.start + makespan b.jobs.toFinset (batchSchedule P A I b)

noncomputable def assembled {D : Type} (P : Protocol D) (A : BaseAlgorithm D)
    (I : Instance D) : List Batch → Schedule
  | [] => fun _ => default
  | b :: rest => join b.jobs.toFinset (translate b.start (batchSchedule P A I b))
      (assembled P A I rest)

/-- Offline semantics of the fixed event-driven policy. `remaining` is an analysis
variable, never an input to the controller. With no pending jobs this finite trace
ends, while the actual controller continues to idle awaiting an arrival. -/
inductive BatchExecution {D : Type} (P : Protocol D) (A : BaseAlgorithm D)
    (I : Instance D) : Finset ℕ → ℝ≥0 → List Batch → Prop
  | done (t : ℝ≥0) : BatchExecution P A I ∅ t []
  | next (remaining : Finset ℕ) (t : ℝ≥0) (b : Batch) (rest : List Batch)
      (nonempty : b.jobs ≠ []) (nodup : b.jobs.Nodup)
      (waiting : b.jobs.toFinset = remaining.filter (fun j => I.release j ≤ b.start))
      (start : b.start = t ∨
        (t < b.start ∧ (∀ j ∈ remaining, b.start ≤ I.release j) ∧
          ∃ j ∈ remaining, I.release j = b.start))
      (tail : BatchExecution P A I (remaining \ b.jobs.toFinset)
        (batchFinish P A I b) rest) :
      BatchExecution P A I remaining t (b :: rest)

/-- The environment delivers exactly the arrivals and batch-completion events,
merging simultaneous events. There is no event announcing the final arrival. -/
def EventsFor {D : Type} (P : Protocol D) (A : BaseAlgorithm D)
    (I : Instance D) (bs : List Batch) (es : List Packet) : Prop :=
  es.Pairwise (fun a b => a.time < b.time) ∧
  (es.flatMap Packet.arrivals).Nodup ∧
  (es.flatMap Packet.arrivals).toFinset = I.jobs ∧
  (∀ e ∈ es, e.arrivals =
    (I.jobs.filter (fun j => I.release j = e.time)).sort (· ≤ ·)) ∧
  (∀ e ∈ es, ∀ j ∈ e.arrivals, I.release j = e.time) ∧
  (∀ e ∈ es, e.finished = true ↔ ∃ b ∈ bs, batchFinish P A I b = e.time) ∧
  (∀ b ∈ bs, ∃ e ∈ es, e.time = batchFinish P A I b ∧ e.finished = true) ∧
  (∀ e ∈ es, e.arrivals ≠ [] ∨ e.finished = true)

noncomputable def computationCost {D : Type} (P : Protocol D) (A : BaseAlgorithm D)
    (I : Instance D) (bs : List Batch) (es : List Packet) : ℕ :=
  (controllerRun es).2.2 +
    (bs.map (fun b => (baseState P A (b.jobs.map (fun j => (j, I.data j)))).cost)).sum

noncomputable def releasedInputSize {D : Type} (P : Protocol D) (I : Instance D) : ℕ :=
  inputSize P (batchData I I.jobs) + I.jobs.card

end ShmoysOnline.ReleaseDates

END IMPORTED LEAN FOR BLIND AUDIT -/
